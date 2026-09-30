//! era-5c witnesses for the null-join discharge (E5C-1) and the formal-zero
//! covered traversal argument (E5C-2). The dataflow witnesses read
//! `NullPaths` directly and need no pin; the emission witnesses run the
//! probe in a child process with `CRAT_ERA5C_MOVE_TRACKING` pinned, since a
//! pin is read once per process.

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{BasicBlock, Local, TerminatorKind};

use super::null_paths::{NullPaths, NullPlace, Proj};

const DECLS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables)]
use core::ffi::c_void;
unsafe extern "C" { fn free(p: *mut c_void); fn touch(p: *mut N) -> i32; fn touch2(p: *mut N, k: i32) -> i32; }
#[repr(C)] pub struct N { pub k: i32, pub l: *mut N, pub r: *mut N }
"#;

/// bst's `deleteNode` shape: the `left == NULL` arm moves `right` out and frees
/// the node; the other arm returns the node.
const DELETE_SHAPE: &str = r#"
pub unsafe fn del(root: *mut N) -> *mut N {
    if root.is_null() { return root; }
    if (*root).l.is_null() {
        let t = (*root).r;
        free(root as *mut c_void);
        return t;
    }
    return root;
}
"#;

fn with_body(
    code: &str,
    name: &str,
    check: impl for<'tcx> FnOnce(rustc_middle::ty::TyCtxt<'tcx>, &rustc_middle::mir::Body<'tcx>) + Send,
) {
    let source = format!("{DECLS}\n{code}");
    ::utils::compilation::run_compiler_on_str(&source, move |tcx| {
        let function = tcx
            .hir_crate(())
            .owners
            .iter()
            .filter_map(|owner| owner.as_owner())
            .filter_map(|owner| match owner.node() {
                OwnerNode::Item(item) if matches!(item.kind, ItemKind::Fn { .. }) => {
                    Some(item.owner_id.def_id)
                }
                _ => None,
            })
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
            .expect("fixture function");
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        check(tcx, &body);
    })
    .unwrap();
}

fn place(local: u32, proj: &[Proj]) -> NullPlace {
    NullPlace {
        local: Local::from_u32(local),
        proj: proj.iter().copied().collect(),
    }
}

/// The edges into the block whose terminator is `return`.
fn return_edges(body: &rustc_middle::mir::Body<'_>) -> Vec<(BasicBlock, BasicBlock)> {
    let exit = body
        .basic_blocks
        .iter_enumerated()
        .find(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Return))
        .map(|(bb, _)| bb)
        .expect("one return block");
    body.basic_blocks.predecessors()[exit]
        .iter()
        .map(|&pred| (pred, exit))
        .collect()
}

/// The edges out of a block that ends in `free(..)`: the edge into its return
/// target.
fn free_successor_edge(body: &rustc_middle::mir::Body<'_>) -> (BasicBlock, BasicBlock) {
    body.basic_blocks
        .iter_enumerated()
        .find_map(|(bb, data)| match &data.terminator().kind {
            TerminatorKind::Call {
                func,
                target: Some(target),
                ..
            } if format!("{func:?}").contains("free") => Some((bb, *target)),
            _ => None,
        })
        .expect("a free call with a return target")
}

#[test]
fn e5c_w1_the_null_field_fact_reaches_the_free_arm_and_the_join() {
    with_body(DELETE_SHAPE, "del", |tcx, body| {
        let paths = NullPaths::compute(tcx, body);
        let left = place(1, &[Proj::Deref, Proj::Field(1)]);
        let (free_bb, after_free) = free_successor_edge(body);
        assert!(
            paths.null_on_edge(free_bb, after_free, &left),
            "`(*root).l` is null on the free arm"
        );
        let edges = return_edges(body);
        assert!(edges.len() >= 2, "the return joins several arms: {edges:?}");
        let on_join: Vec<bool> = edges
            .iter()
            .map(|&(pred, succ)| paths.null_on_edge(pred, succ, &left))
            .collect();
        assert!(
            on_join.iter().any(|&b| b) && on_join.iter().any(|&b| !b),
            "the left-null fact reaches the join on the free arm only: {on_join:?}"
        );
        // The `root == NULL` arm carries the whole-local fact to the join.
        let root = place(1, &[]);
        assert!(
            edges
                .iter()
                .any(|&(pred, succ)| paths.null_on_edge(pred, succ, &root)),
            "`root` is null on the early-return arm"
        );
    });
}

#[test]
fn e5c_w2_a_call_between_the_test_and_the_join_kills_the_field_fact() {
    with_body(
        r#"
pub unsafe fn del(root: *mut N) -> *mut N {
    if (*root).l.is_null() {
        touch(root);
        return root;
    }
    return root;
}
"#,
        "del",
        |tcx, body| {
            let paths = NullPaths::compute(tcx, body);
            let left = place(1, &[Proj::Deref, Proj::Field(1)]);
            for (pred, succ) in return_edges(body) {
                assert!(
                    !paths.null_on_edge(pred, succ, &left),
                    "an opaque call may have written `(*root).l`"
                );
            }
        },
    );
}

#[test]
fn e5c_w3_a_store_through_a_pointer_kills_the_field_fact() {
    with_body(
        r#"
pub unsafe fn del(root: *mut N, q: *mut N, x: *mut N) -> *mut N {
    if (*root).l.is_null() {
        (*q).l = x;
        return root;
    }
    return root;
}
"#,
        "del",
        |tcx, body| {
            let paths = NullPaths::compute(tcx, body);
            let left = place(1, &[Proj::Deref, Proj::Field(1)]);
            for (pred, succ) in return_edges(body) {
                assert!(
                    !paths.null_on_edge(pred, succ, &left),
                    "`q` may alias `root`; the store kills the fact"
                );
            }
        },
    );
}

#[test]
fn e5c_w4_the_non_null_arm_carries_no_fact_and_a_negated_test_swaps_the_arms() {
    with_body(
        r#"
pub unsafe fn del(root: *mut N) -> *mut N {
    if !(*root).l.is_null() {
        return (*root).l;
    }
    return root;
}
"#,
        "del",
        |tcx, body| {
            let paths = NullPaths::compute(tcx, body);
            let left = place(1, &[Proj::Deref, Proj::Field(1)]);
            let edges = return_edges(body);
            let on_join: Vec<bool> = edges
                .iter()
                .map(|&(pred, succ)| paths.null_on_edge(pred, succ, &left))
                .collect();
            // Exactly one arm (the `else`, reached when the negated test is
            // false, i.e. the pointer IS null) carries the fact.
            assert_eq!(
                on_join.iter().filter(|&&b| b).count(),
                1,
                "one null arm through the negation: {on_join:?}"
            );
        },
    );
}

#[test]
fn e5c_w5_vacuous_components_follow_the_window_layout() {
    with_body(DELETE_SHAPE, "del", |tcx, body| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let crate_ctxt = super::CrateCtxt::new(&program);
        let struct_ctxt = crate_ctxt
            .struct_ctxt
            .with_max_precision(super::BO_PRECISION);
        let ty = body.local_decls[Local::from_u32(1)].ty;
        let left = place(1, &[Proj::Deref, Proj::Field(1)]);
        let right = place(1, &[Proj::Deref, Proj::Field(2)]);
        let root = place(1, &[]);
        let window = 3;
        assert_eq!(
            super::null_paths::vacuous_components_with(
                tcx,
                &struct_ctxt,
                ty,
                window,
                &[left.clone()]
            ),
            vec![false, true, false]
        );
        assert_eq!(
            super::null_paths::vacuous_components_with(tcx, &struct_ctxt, ty, window, &[right]),
            vec![false, false, true]
        );
        assert_eq!(
            super::null_paths::vacuous_components_with(tcx, &struct_ctxt, ty, window, &[root]),
            vec![true, true, true]
        );
        assert_eq!(
            super::null_paths::vacuous_components_with(tcx, &struct_ctxt, ty, window, &[]),
            vec![false, false, false]
        );
    });
}

/// The recorded equations of the fixture, under whatever arm this process
/// pins. `CRAT_E5C_INNER` selects the fixture in the child.
fn null_join_rows(code: &str) -> usize {
    let mut rows = 0;
    super::licensing::graph_tests::with_facts(&format!("{DECLS}\n{code}"), |facts| {
        rows = facts
            .equations
            .iter()
            .filter(|row| row.operation == "null-join" && row.point.phase == "phi")
            .count();
    });
    rows
}

#[test]
fn e5c_w6_the_default_arm_emits_no_null_join() {
    assert!(
        !super::null_paths::move_tracking(),
        "the suite runs with the arm off"
    );
    assert_eq!(null_join_rows(DELETE_SHAPE), 0);
}

#[test]
#[ignore = "runs under CRAT_ERA5C_MOVE_TRACKING=on in a child of e5c_w7"]
fn e5c_inner_null_join_rows_under_the_arm() {
    assert!(super::null_paths::move_tracking());
    let rows = null_join_rows(DELETE_SHAPE);
    eprintln!("E5C_NULL_JOIN_ROWS={rows}");
    assert!(
        rows >= 2,
        "the free arm discharges `left`, the null arm discharges `root`: {rows}"
    );
}

fn child(test: &str, env: &[(&str, &str)]) -> String {
    let exe = std::env::current_exe().expect("current_exe");
    let mut command = std::process::Command::new(exe);
    command.args([
        test,
        "--exact",
        "--ignored",
        "--nocapture",
        "--test-threads=1",
    ]);
    for (key, value) in env {
        command.env(key, value);
    }
    let output = command.output().expect("child test");
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "child {test} failed:\n{text}");
    text
}

#[test]
fn e5c_w7_the_arm_emits_null_join_rows_at_the_free_and_null_arms() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_null_join_rows_under_the_arm",
        &[("CRAT_ERA5C_MOVE_TRACKING", "on")],
    );
    assert!(text.contains("E5C_NULL_JOIN_ROWS="), "{text}");
}

const BST: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/rs-crown-derived/bst/lib.rs"
);
const BST_TARGETS: &str = "src::bst::node::field1@d0=own,src::bst::node::field2@d0=own,\
src::bst::newNode::_0@d0=own,src::bst::newNode::_3@d0=own,src::bst::insert::_0@d0=own,\
src::bst::insert::_1@d0=own,src::bst::deleteNode::_0@d0=own,src::bst::deleteNode::_1@d0=own,\
src::bst::minValueNode::_0@d0=ref,src::bst::minValueNode::_1@d0=ref,src::bst::inorder::_1@d0=ref";

fn bst_probe(arm: &str) -> String {
    let dir = std::env::var("DIR")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/../..").to_owned());
    child(
        "bo_c1::r385_forced_assignment_probe",
        &[
            ("CRAT_R385_PROGRAM", BST),
            ("CRAT_R385_TARGETS", BST_TARGETS),
            ("CRAT_R385_GRANULARITY", "assertion"),
            ("CRAT_R385_WORLD", "closed"),
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", arm),
            ("CRAT_ERA5C_DEBUG", "1"),
            ("DIR", dir.as_str()),
        ],
    )
}

/// W (charter §2): bst's all-safe assignment (fields own, producers own, the
/// readers ref) is SAT under the arm in the attested closed world.
#[test]
fn e5c_w8_bst_all_safe_is_sat_under_the_arm() {
    if !std::path::Path::new(BST).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let text = bst_probe("on");
    assert!(text.contains("R385 VERDICT=SAT"), "{text}");
    assert!(!text.contains("E5C traversal-pending"), "{text}");
}

/// The control: the same assignment is UNSAT with the arm off, and the
/// traversal licence refuses for the unmatched deeper formals (E5C-2's
/// premise), so the arm-off system is byte-identical to the base.
#[test]
fn e5c_w9_bst_all_safe_is_unsat_without_the_arm() {
    if !std::path::Path::new(BST).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let text = bst_probe("off");
    assert!(text.contains("R385 VERDICT=UNSAT"), "{text}");
    assert!(text.contains("reason=argument-formal-unmatched"), "{text}");
}

/// bst's four pointer functions verbatim (the derived substrate's `lib.rs`
/// minus the crate attributes), run through the FULL solve — the joint pass
/// with borrow verification, retirement and the relax loop — the way the
/// corpus worker runs it. Printed per slot; asserted on the fields.
const BST_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; fn free(_: *mut core::ffi::c_void); fn printf(_: *const i8, _: ...) -> i32; }
#[repr(C)] pub struct node { pub key: i32, pub left: *mut node, pub right: *mut node }
pub unsafe fn newNode(item: i32) -> *mut node {
    let mut temp = malloc(core::mem::size_of::<node>() as u64) as *mut node;
    (*temp).key = item; (*temp).left = 0 as *mut node; (*temp).right = 0 as *mut node;
    return temp;
}
pub unsafe fn inorder(root: *mut node) {
    if !root.is_null() { inorder((*root).left); printf(b"%d \0" as *const u8 as *const i8, (*root).key); inorder((*root).right); }
}
pub unsafe fn insert(node: *mut node, key: i32) -> *mut node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key { (*node).left = insert((*node).left, key); } else { (*node).right = insert((*node).right, key); }
    return node;
}
pub unsafe fn minValueNode(mut node: *mut node) -> *mut node {
    while !node.is_null() && !((*node).left).is_null() { node = (*node).left; }
    return node;
}
pub unsafe fn deleteNode(root: *mut node, key: i32) -> *mut node {
    if root.is_null() { return root; }
    if key < (*root).key { (*root).left = deleteNode((*root).left, key); }
    else if key > (*root).key { (*root).right = deleteNode((*root).right, key); }
    else {
        if ((*root).left).is_null() { let temp = (*root).right; free(root as *mut core::ffi::c_void); return temp; }
        else { if ((*root).right).is_null() { let temp_0 = (*root).left; free(root as *mut core::ffi::c_void); return temp_0; } }
        let temp_1 = minValueNode((*root).right);
        (*root).key = (*temp_1).key;
        (*root).right = deleteNode((*root).right, (*temp_1).key);
    }
    return root;
}
"#;

/// The full solve of the bst shape under whatever arm this process pins,
/// printed as `E5C_MODEL <slot> <kind>` lines.
fn bst_shape_model() -> Vec<(String, String)> {
    shape_model(BST_SHAPE)
}

/// L01^5 (i) RED: bst's shape with BOTH `free` calls removed — avl's situation
/// (an allocation the program never frees). Nothing else differs from
/// `BST_SHAPE`, so any model difference is the missing sink alone.
const BST_LEAK_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; fn printf(_: *const i8, _: ...) -> i32; }
#[repr(C)] pub struct node { pub key: i32, pub left: *mut node, pub right: *mut node }
pub unsafe fn newNode(item: i32) -> *mut node {
    let mut temp = malloc(core::mem::size_of::<node>() as u64) as *mut node;
    (*temp).key = item; (*temp).left = 0 as *mut node; (*temp).right = 0 as *mut node;
    return temp;
}
pub unsafe fn inorder(root: *mut node) {
    if !root.is_null() { inorder((*root).left); printf(b"%d \0" as *const u8 as *const i8, (*root).key); inorder((*root).right); }
}
pub unsafe fn insert(node: *mut node, key: i32) -> *mut node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key { (*node).left = insert((*node).left, key); } else { (*node).right = insert((*node).right, key); }
    return node;
}
pub unsafe fn minValueNode(mut node: *mut node) -> *mut node {
    while !node.is_null() && !((*node).left).is_null() { node = (*node).left; }
    return node;
}
pub unsafe fn deleteNode(root: *mut node, key: i32) -> *mut node {
    if root.is_null() { return root; }
    if key < (*root).key { (*root).left = deleteNode((*root).left, key); }
    else if key > (*root).key { (*root).right = deleteNode((*root).right, key); }
    else {
        if ((*root).left).is_null() { let temp = (*root).right; return temp; }
        else { if ((*root).right).is_null() { let temp_0 = (*root).left; return temp_0; } }
        let temp_1 = minValueNode((*root).right);
        (*root).key = (*temp_1).key;
        (*root).right = deleteNode((*root).right, (*temp_1).key);
    }
    return root;
}
"#;

/// L01^5 (i) diagnosis W18: the SAME shape with and without its frees. With the
/// frees the fields are `Owning` (W10). Without them the leak-parity waiver says
/// the allocation may still be owned — today it is not, and this test records
/// which way the model falls so the rule is built against a measured mechanism.
#[test]
#[ignore = "runs under CRAT_ERA5C_MOVE_TRACKING=on in a child of e5c_w18"]
fn e5c_inner_bst_leak_shape_full_solve_under_the_arm() {
    assert!(super::null_paths::move_tracking());
    let rows = shape_model(BST_LEAK_SHAPE);
    let kinds = |needle: &str| -> Vec<String> {
        rows.iter()
            .filter(|(k, _)| k.contains(needle))
            .map(|(k, v)| format!("{k}={v}"))
            .collect()
    };
    eprintln!("E5C_LEAK fields: {:?}", kinds("node::field"));
    eprintln!("E5C_LEAK newNode: {:?}", kinds("newNode::"));
    let owning = rows.iter().filter(|(_, v)| v == "owning").count();
    let raw = rows.iter().filter(|(_, v)| v == "raw").count();
    eprintln!(
        "E5C_LEAK totals: raw={raw} owning={owning} of {}",
        rows.len()
    );
}

/// L01^5 (i) RED W19: avl's OWN shape — the rotations that permute three field
/// slots between two nodes, plus `newNode`'s malloc and NO `free` anywhere. This
/// separates the two candidate causes: W18 showed a missing sink alone costs
/// Owning but leaves Ref, so whatever makes the corpus avl 53/12/0 must be here.
const AVL_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct Node { pub key: i32, pub height: i32, pub left: *mut Node, pub right: *mut Node }
pub unsafe fn height(n: *mut Node) -> i32 { if n.is_null() { return 0; } return (*n).height; }
pub unsafe fn newNode(key: i32) -> *mut Node {
    let mut node = malloc(core::mem::size_of::<Node>() as u64) as *mut Node;
    (*node).key = key; (*node).left = 0 as *mut Node; (*node).right = 0 as *mut Node; (*node).height = 1;
    return node;
}
pub unsafe fn rightRotate(y: *mut Node) -> *mut Node {
    let x = (*y).left;
    let T2 = (*x).right;
    (*x).right = y;
    (*y).left = T2;
    (*y).height = height((*y).left) + 1;
    (*x).height = height((*x).left) + 1;
    return x;
}
pub unsafe fn leftRotate(x: *mut Node) -> *mut Node {
    let y = (*x).right;
    let T2 = (*y).left;
    (*y).left = x;
    (*x).right = T2;
    (*x).height = height((*x).left) + 1;
    (*y).height = height((*y).left) + 1;
    return y;
}
pub unsafe fn insert(node: *mut Node, key: i32) -> *mut Node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key { (*node).left = insert((*node).left, key); }
    else { (*node).right = insert((*node).right, key); }
    if key < (*(*node).left).key { return rightRotate(node); }
    return leftRotate(node);
}
"#;

/// W20: avl's shape WITH a free site — the last control. If the rotations are
/// the cause of the Raw, adding a sink does not rescue them; if the missing sink
/// were the cause, this model would move.
const AVL_WITH_FREE_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; fn free(_: *mut core::ffi::c_void); }
#[repr(C)] pub struct Node { pub key: i32, pub height: i32, pub left: *mut Node, pub right: *mut Node }
pub unsafe fn height(n: *mut Node) -> i32 { if n.is_null() { return 0; } return (*n).height; }
pub unsafe fn newNode(key: i32) -> *mut Node {
    let mut node = malloc(core::mem::size_of::<Node>() as u64) as *mut Node;
    (*node).key = key; (*node).left = 0 as *mut Node; (*node).right = 0 as *mut Node; (*node).height = 1;
    return node;
}
pub unsafe fn rightRotate(y: *mut Node) -> *mut Node {
    let x = (*y).left;
    let T2 = (*x).right;
    (*x).right = y;
    (*y).left = T2;
    (*y).height = height((*y).left) + 1;
    (*x).height = height((*x).left) + 1;
    return x;
}
pub unsafe fn leftRotate(x: *mut Node) -> *mut Node {
    let y = (*x).right;
    let T2 = (*y).left;
    (*y).left = x;
    (*x).right = T2;
    (*x).height = height((*x).left) + 1;
    (*y).height = height((*y).left) + 1;
    return y;
}
pub unsafe fn insert(node: *mut Node, key: i32) -> *mut Node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key { (*node).left = insert((*node).left, key); }
    else { (*node).right = insert((*node).right, key); }
    if key < (*(*node).left).key { return rightRotate(node); }
    return leftRotate(node);
}
pub unsafe fn dropLeaf(n: *mut Node) {
    if ((*n).left).is_null() { free(n as *mut core::ffi::c_void); }
}
"#;

/// W20 inner: avl's shape with a free, under the arm.
#[test]
#[ignore = "runs under CRAT_ERA5C_MOVE_TRACKING=on in a child of e5c_w20"]
fn e5c_inner_avl_with_free_full_solve_under_the_arm() {
    assert!(super::null_paths::move_tracking());
    let rows = shape_model(AVL_WITH_FREE_SHAPE);
    let raw = rows.iter().filter(|(_, v)| v == "raw").count();
    let refs = rows.iter().filter(|(_, v)| v == "ref").count();
    let own = rows.iter().filter(|(_, v)| v == "owning").count();
    let fields: Vec<String> = rows
        .iter()
        .filter(|(k, _)| k.contains("Node::field"))
        .map(|(k, v)| format!("{k}={v}"))
        .collect();
    eprintln!("E5C_AVLFREE fields: {fields:?}");
    eprintln!(
        "E5C_AVLFREE totals: raw={raw} ref={refs} owning={own} of {}",
        rows.len()
    );
}

/// W20: avl with a free — the control that separates the rotation from the sink.
#[test]
fn e5c_w20_avl_with_a_free_is_measured() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_avl_with_free_full_solve_under_the_arm",
        &[
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", "on"),
        ],
    );
    assert!(text.contains("E5C_AVLFREE totals"), "{text}");
    eprintln!(
        "{}",
        text.lines()
            .filter(|l| l.contains("E5C_AVLFREE"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// R459-3(2) / relay 028 -- the USER side check, NON-CITABLE: does bst all-safe
/// model survive `main_0` / `main` being uncommented? The source is read from disk
/// (the derived corpus form, and the same form with the commented block restored
/// verbatim), so this is the corpus program, not a hand-written shape.
#[test]
#[ignore = "runs under the arms in a child of e5c_w21"]
fn e5c_inner_bst_main_side_check() {
    assert!(super::null_paths::move_tracking());
    for (name, path) in [
        (
            "CORPUS",
            "/home/p51lee/dev/.crat-scratch/era-5c/bst-main/lib-corpus.rs",
        ),
        (
            "VARIANT",
            "/home/p51lee/dev/.crat-scratch/era-5c/bst-main/lib-variant.rs",
        ),
    ] {
        let source = std::fs::read_to_string(path).expect("side-check source");
        let rows = shape_model(&source);
        let raw = rows.iter().filter(|(_, v)| v == "raw").count();
        let refs = rows.iter().filter(|(_, v)| v == "ref").count();
        let own = rows.iter().filter(|(_, v)| v == "owning").count();
        eprintln!(
            "E5C_SIDE {name} totals: raw={raw} ref={refs} owning={own} of {}",
            rows.len()
        );
        for (k, v) in &rows {
            eprintln!("E5C_SIDE {name} {k} {v}");
        }
    }
}

/// W21: the side check at **L01⁵** -- the L01⁗ arms plus L01⁵'s two pins,
/// which are fail-loud and default to OFF, so a witness that does not set them
/// measures L01⁗ however far the frame has moved (R510-1(3); era-5c report 033
/// §1a measured the pin matrix by hand because of exactly this).
#[test]
fn e5c_w21_bst_main_side_check_at_l01p5() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_bst_main_side_check",
        &[
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", "on"),
            ("CRAT_ERA5C_FIELD_MOVE", "on"),
            ("CRAT_ERA5C_LEAK_PARITY", "on"),
            // Pin the arm explicitly: these two witnesses record the frame
            // WITHOUT A1, and must not drift with the ambient environment.
            ("CRAT_ERA5C_RESEAT_A1", "off"),
        ],
    );
    assert!(text.contains("E5C_SIDE VARIANT totals"), "{text}");
    // 033 §1a: the corpus form solves clean and the driver variant collapses,
    // and L01⁵'s pins move neither. Pinned so a future frame that DOES move one
    // of them fails here instead of passing quietly.
    assert!(
        text.contains("E5C_SIDE CORPUS totals: raw=0 ref=13 owning=31"),
        "{text}"
    );
    assert!(
        text.contains("E5C_SIDE VARIANT totals: raw=59 ref=38 owning=0"),
        "{text}"
    );
}

/// **W21c** — the same side check with **L01⁷-A1 on**. This is the criterion
/// R517-12 set and report 039 measured: the corpus form is untouched and the
/// driver's collapse is repaired outright. A1 spares exactly one local here,
/// `main_0::_2` (`root`), the destination of `root = insert(root, k)`.
#[test]
fn e5c_w21c_bst_main_side_check_under_a1() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_bst_main_side_check",
        &[
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", "on"),
            ("CRAT_ERA5C_FIELD_MOVE", "on"),
            ("CRAT_ERA5C_LEAK_PARITY", "on"),
            ("CRAT_ERA5C_RESEAT_A1", "on"),
        ],
    );
    assert!(
        text.contains("E5C_SIDE CORPUS totals: raw=0 ref=13 owning=31"),
        "{text}"
    );
    assert!(
        text.contains("E5C_SIDE VARIANT totals: raw=0 ref=39 owning=58"),
        "{text}"
    );
}

/// W21's control: the same side check with the **L01⁗** arms only. R510-1(3)
/// keeps it so the two frames are compared rather than silently swapped.
#[test]
fn e5c_w21b_bst_main_side_check_at_l01pppp_control() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_bst_main_side_check",
        &[
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", "on"),
            ("CRAT_ERA5C_FIELD_MOVE", "off"),
            ("CRAT_ERA5C_LEAK_PARITY", "off"),
            ("CRAT_ERA5C_RESEAT_A1", "off"),
        ],
    );
    assert!(
        text.contains("E5C_SIDE CORPUS totals: raw=0 ref=13 owning=31"),
        "{text}"
    );
    assert!(
        text.contains("E5C_SIDE VARIANT totals: raw=59 ref=38 owning=0"),
        "{text}"
    );
}

/// R464-2(1) / 019: one derived corpus source, whatever arms this process pins,
/// so the memory cost of each arm can be measured with `/usr/bin/time -v`.
/// `CRAT_E5C_SIDE_SOURCE` names the file.
#[test]
#[ignore = "driven by the 019 memory bisect"]
fn e5c_inner_solve_named_source() {
    let path = std::env::var("CRAT_E5C_SIDE_SOURCE").expect("CRAT_E5C_SIDE_SOURCE");
    let source = std::fs::read_to_string(&path).expect("source");
    let rows = shape_model(&source);
    // Report 043: dump every slot's kind so subjects can be joined by key.
    if let Ok(out) = std::env::var("CRAT_E5C_SIDE_ROWS") {
        let text: String = rows.iter().map(|(k, v)| format!("{k}\t{v}\n")).collect();
        std::fs::write(&out, text).expect("write side rows");
    }
    let raw = rows.iter().filter(|(_, v)| v == "raw").count();
    let refs = rows.iter().filter(|(_, v)| v == "ref").count();
    let own = rows.iter().filter(|(_, v)| v == "owning").count();
    eprintln!(
        "E5C_BISECT {path} raw={raw} ref={refs} owning={own} slots={}",
        rows.len()
    );
}

/// W19 inner: avl's shape through the full solve under the arm.
#[test]
#[ignore = "runs under CRAT_ERA5C_MOVE_TRACKING=on in a child of e5c_w19"]
fn e5c_inner_avl_shape_full_solve_under_the_arm() {
    assert!(super::null_paths::move_tracking());
    let rows = shape_model(AVL_SHAPE);
    let kinds = |needle: &str| -> Vec<String> {
        rows.iter()
            .filter(|(k, _)| k.contains(needle))
            .map(|(k, v)| format!("{k}={v}"))
            .collect()
    };
    eprintln!("E5C_AVL fields: {:?}", kinds("Node::field"));
    eprintln!("E5C_AVL newNode: {:?}", kinds("newNode::"));
    eprintln!("E5C_AVL rightRotate: {:?}", kinds("rightRotate::"));
    let raw = rows.iter().filter(|(_, v)| v == "raw").count();
    let refs = rows.iter().filter(|(_, v)| v == "ref").count();
    let own = rows.iter().filter(|(_, v)| v == "owning").count();
    eprintln!(
        "E5C_AVL totals: raw={raw} ref={refs} owning={own} of {}",
        rows.len()
    );
}

/// W19: avl's shape, measured in a child with the arm on.
#[test]
fn e5c_w19_the_avl_shape_model_is_measured() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_avl_shape_full_solve_under_the_arm",
        &[
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", "on"),
        ],
    );
    assert!(text.contains("E5C_AVL totals"), "{text}");
    eprintln!(
        "{}",
        text.lines()
            .filter(|l| l.contains("E5C_AVL"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// W18: the leak shape's model, measured in a child with the arm on.
#[test]
fn e5c_w18_the_leak_shape_model_is_measured() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_bst_leak_shape_full_solve_under_the_arm",
        &[
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", "on"),
        ],
    );
    assert!(text.contains("E5C_LEAK totals"), "{text}");
    eprintln!(
        "{}",
        text.lines()
            .filter(|l| l.contains("E5C_LEAK"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// The full solve — the joint pass with borrow verification, retirement and
/// the relax loop, the way the corpus worker runs it — of a fixture, under
/// whatever arms this process pins.
fn shape_model(code: &str) -> Vec<(String, String)> {
    use rustc_hir::{ItemKind, OwnerNode};
    let mut rows = Vec::new();
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = super::crate_slots::CrateSlots::build(&program);
        let origins = super::origins::compute_origins(&program);
        let mutability = super::mutability_facts::MutFacts::from_program(&program);
        let verified = super::construction::solve_bo_a5_config(
            &program,
            &slots,
            &origins,
            &mutability,
            super::a5_overlap::A5Mode::PreciseReplay,
            Some(super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        )
        .expect("the shape solves");
        // R609-3 (080 / 074): the raw-cause ledger of this model, as the entry's
        // sidecar would carry it, when a path is named.
        if let Ok(path) = std::env::var("CRAT_E5C_SIDE_LEDGER") {
            let program =
                std::env::var("CRAT_E5C_SIDE_PROGRAM").unwrap_or_else(|_| "shape".to_owned());
            // `prepare` (inside the solve) already took the ledger that explains
            // this model for its own sidecar; `last` is that ledger.
            let rows = super::raw_cause::last().expect("the ledger is on and explains the model");
            let mut text = format!("{}\n", super::raw_cause::HEADER);
            for row in &rows {
                text.push_str(&format!("{program}\t{}\n", row.sidecar()));
            }
            std::fs::write(&path, text).expect("the ledger sidecar");
            eprintln!("E5C_LEDGER {path} rows={}", rows.len());
        }
        // R617-1: the receipt's repair stamp (only a guarded run has one).
        for line in verified.receipt.lines() {
            if line.starts_with("repair=") || line.starts_with("guarded_") {
                eprintln!("E5C_REPAIR {line}");
            }
        }
        // R612-2 (080's over-pin read): the Mode-A commit totals and A5's
        // may-overlap parameter pairs, beside the ledger.
        if let Ok(path) = std::env::var("CRAT_E5C_SIDE_STATS") {
            let stats = &verified.round_stats;
            let mut text = format!(
                "rounds\t{}\ncommits_conflict\t{}\ncommits_per_round\t{:?}\n",
                stats.rounds, stats.commits_conflict, stats.commits_per_round
            );
            for line in verified.summary_artifact.summary_tsv.lines().skip(1) {
                let fields: Vec<&str> = line.split('\t').collect();
                let Some(function) = fields.first().and_then(|f| f.parse::<u32>().ok()) else {
                    continue;
                };
                let did = rustc_span::def_id::LocalDefId {
                    local_def_index: rustc_span::def_id::DefIndex::from_u32(function),
                };
                text.push_str(&format!(
                    "a5_pair\t{}\t{}\t{}\n",
                    tcx.def_path_str(did.to_def_id()),
                    fields[1],
                    fields[2]
                ));
            }
            std::fs::write(&path, text).expect("the side stats");
        }
        for (slot, kind) in &verified.model {
            let key = match slot {
                super::SlotRef::Local(function, id) => {
                    let universe = &slots.fn_local_slots[function];
                    let s = universe.slot(*id);
                    let super::slots::SlotOwner::Local(local) = s.owner else { unreachable!() };
                    super::slot_key::local_key(tcx, *function, local.as_usize(), s.depth)
                }
                super::SlotRef::Field(id) => {
                    let s = slots.field_slots.slot(*id);
                    let super::slots::SlotOwner::Field(field) = s.owner else { unreachable!() };
                    super::slot_key::field_key(tcx, field.struct_did, field.field_index, s.depth)
                }
            };
            rows.push((key, format!("{kind:?}").to_lowercase()));
        }
    })
    .unwrap();
    rows.sort();
    for (k, v) in &rows {
        eprintln!("E5C_MODEL {k} {v}");
    }
    rows
}

#[test]
#[ignore = "runs under CRAT_ERA5C_MOVE_TRACKING=on in a child of e5c_w10"]
fn e5c_inner_bst_shape_full_solve_under_the_arm() {
    assert!(super::null_paths::move_tracking());
    let rows = bst_shape_model();
    let kind = |k: &str| {
        rows.iter()
            .find(|(key, _)| key == k)
            .map(|(_, v)| v.clone())
    };
    assert_eq!(
        kind("node::field1@d0").as_deref(),
        Some("owning"),
        "{rows:?}"
    );
    assert_eq!(
        kind("node::field2@d0").as_deref(),
        Some("owning"),
        "{rows:?}"
    );
}

/// E5C-3's RED: the full solve of the bst shape leaves the node fields raw
/// under E5C-1/E5C-2 alone (the borrow-side `¬ref` on the traversal receiver
/// leaks both free sinks); GREEN = both fields `owning`.
#[test]
fn e5c_w10_bst_shape_fields_own_under_the_arm() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_bst_shape_full_solve_under_the_arm",
        &[
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", "on"),
            ("CRAT_ERA5C_DEBUG", "1"),
        ],
    );
    assert!(text.contains("E5C_MODEL"), "{text}");
}

/// E5C-3's predicate on MIR: bst's `_40 = copy (*root).right` (the recursive
/// call's argument, bb18) defers to the block's call terminator because the
/// statements between it and the call are pure reads; with a store in between
/// it does not. Runs under the pin in a child (the predicate is pin-gated).
#[test]
#[ignore = "runs under CRAT_ERA5C_MOVE_TRACKING=on in a child of e5c_w11"]
fn e5c_inner_deferred_argument_read_shape() {
    use rustc_middle::mir::{Location, Rvalue, StatementKind, TerminatorKind};
    assert!(super::null_paths::move_tracking());
    let deferrals = |code: &str| -> Vec<(u32, usize, Option<usize>)> {
        let mut rows = Vec::new();
        with_body(code, "del", |tcx, body| {
            for (bb, data) in body.basic_blocks.iter_enumerated() {
                if !matches!(data.terminator().kind, TerminatorKind::Call { .. }) {
                    continue;
                }
                for (index, statement) in data.statements.iter().enumerate() {
                    let StatementKind::Assign(assign) = &statement.kind else { continue };
                    // The pointer field copy `_ = copy (*root).r` only.
                    let Rvalue::Use(operand) = &assign.1 else { continue };
                    if !operand.place().is_some_and(|p| {
                        !p.projection.is_empty() && p.ty(body, tcx).ty.is_raw_ptr()
                    }) {
                        continue;
                    }
                    let location = Location {
                        block: bb,
                        statement_index: index,
                    };
                    let deferred = super::null_paths::deferred_argument_read(body, location)
                        .map(|l| l.statement_index);
                    rows.push((bb.as_u32(), index, deferred));
                }
            }
        });
        rows
    };
    // bst's `else` arm: the field copy, then `(*temp).key`, then the call.
    let pure = deferrals(
        r#"
unsafe fn del(root: *mut N, temp: *mut N) -> *mut N {
    touch2((*root).r, (*temp).k);
    return root;
}
"#,
    );
    let field_copy = pure
        .iter()
        .find(|(_, _, d)| d.is_some())
        .unwrap_or_else(|| panic!("the field copy defers to the terminator: {pure:?}"));
    assert!(field_copy.2.unwrap() > field_copy.1, "{pure:?}");
    // A store between the copy and the call: no deferral anywhere.
    let impure = deferrals(
        r#"
unsafe fn del(root: *mut N, temp: *mut N) -> *mut N {
    touch2((*root).r, { (*root).k = 0; (*temp).k });
    return root;
}
"#,
    );
    assert!(
        !impure.is_empty() && impure.iter().all(|(_, _, d)| d.is_none()),
        "{impure:?}"
    );
    eprintln!("E5C_DEFERRAL_OK");
}

#[test]
fn e5c_w11_the_argument_move_defers_only_across_pure_reads() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_deferred_argument_read_shape",
        &[("CRAT_ERA5C_MOVE_TRACKING", "on")],
    );
    assert!(text.contains("E5C_DEFERRAL_OK"), "{text}");
}

// ---------------------------------------------------------------------------
// R409-1: the allocator contract `allocator-contract:brotli-memory-manager/v1`.
// A brotli-shaped memory manager: the default pair is malloc / free, the
// external pair is assumed to honour the same contract.
// ---------------------------------------------------------------------------

const BROTLI_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case)]
use core::ffi::c_void;
extern "C" { fn malloc(_: u64) -> *mut c_void; fn free(_: *mut c_void); fn exit(_: i32) -> !; }
pub type brotli_alloc_func = Option<unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void>;
pub type brotli_free_func = Option<unsafe extern "C" fn(*mut c_void, *mut c_void)>;
#[repr(C)] pub struct MemoryManager { pub alloc_func: brotli_alloc_func, pub free_func: brotli_free_func, pub opaque: *mut c_void }
pub unsafe extern "C" fn BrotliDefaultAllocFunc(opaque: *mut c_void, size: u64) -> *mut c_void { return malloc(size); }
pub unsafe extern "C" fn BrotliDefaultFreeFunc(opaque: *mut c_void, address: *mut c_void) { free(address); }
pub unsafe fn BrotliInitMemoryManager(m: *mut MemoryManager, alloc_func: brotli_alloc_func, free_func: brotli_free_func, opaque: *mut c_void) {
    if alloc_func.is_none() {
        (*m).alloc_func = Some(BrotliDefaultAllocFunc as unsafe extern "C" fn(*mut c_void, u64) -> *mut c_void);
        (*m).free_func = Some(BrotliDefaultFreeFunc as unsafe extern "C" fn(*mut c_void, *mut c_void));
        (*m).opaque = 0 as *mut c_void;
    } else { (*m).alloc_func = alloc_func; (*m).free_func = free_func; (*m).opaque = opaque; }
}
pub unsafe fn BrotliAllocate(m: *mut MemoryManager, n: u64) -> *mut c_void {
    let result = ((*m).alloc_func).expect("non-null function pointer")((*m).opaque, n);
    if result.is_null() { exit(1); }
    return result;
}
pub unsafe fn BrotliFree(m: *mut MemoryManager, p: *mut c_void) {
    ((*m).free_func).expect("non-null function pointer")((*m).opaque, p);
}
pub unsafe fn opaque_of(m: *mut MemoryManager) -> *mut c_void { return (*m).opaque; }
pub unsafe fn make(m: *mut MemoryManager) -> u32 {
    let p = BrotliAllocate(m, 16) as *mut u32;
    *p = 1;
    let v = *p;
    BrotliFree(m, p as *mut c_void);
    return v;
}
pub unsafe fn wrong_free(m: *mut MemoryManager) -> u32 {
    let q = BrotliAllocate(m, 16) as *mut u32;
    *q = 2;
    let v = *q;
    free(q as *mut c_void);
    return v;
}
pub unsafe fn not_an_allocation(m: *mut MemoryManager) -> u32 {
    let o = opaque_of(m) as *mut u32;
    return *o;
}
"#;

/// The full solve of the brotli shape under whatever arms this process pins.
fn brotli_shape_model() -> Vec<(String, String)> {
    shape_model(BROTLI_SHAPE)
}

#[test]
#[ignore = "runs under the contract pin in a child of e5c_w12"]
fn e5c_inner_brotli_shape_full_solve_under_the_contract() {
    assert!(super::allocator_contract::enabled());
    let rows = brotli_shape_model();
    let kind = |k: &str| {
        rows.iter()
            .find(|(key, _)| key == k)
            .map(|(_, v)| v.clone())
    };
    // W12: the wrapper-seeded local (`make::p` = `_4`, the cast of the call
    // result `_3`) decides Owning; the wrapper's own result too.
    assert_eq!(
        kind("make::_4@d0").as_deref(),
        Some("owning"),
        "make::p {rows:?}"
    );
    assert_eq!(kind("make::_3@d0").as_deref(), Some("owning"), "{rows:?}");
    assert_eq!(
        kind("BrotliAllocate::_0@d0").as_deref(),
        Some("owning"),
        "{rows:?}"
    );
    // W13: the BrotliFree sink pairs — the callee's parameter consumes.
    assert_eq!(
        kind("BrotliFree::_2@d0").as_deref(),
        Some("owning"),
        "BrotliFree::p {rows:?}"
    );
    // W14: a wrapper whose return is not the allocation stays opaque: nothing
    // in `not_an_allocation` is Owning.
    assert!(
        rows.iter()
            .all(|(k, v)| !k.starts_with("not_an_allocation::") || v != "owning"),
        "{rows:?}"
    );
    // W15: a contract allocation released through libc `free` is refused
    // Owning (`wrong_free::q` = `_4`), while `make` keeps its token.
    assert_eq!(
        kind("wrong_free::_4@d0").as_deref(),
        Some("raw"),
        "wrong_free::q {rows:?}"
    );
    assert_eq!(
        kind("wrong_free::_3@d0").as_deref(),
        Some("raw"),
        "{rows:?}"
    );
    eprintln!("E5C_CONTRACT_OK");
}

#[test]
fn e5c_w12_to_w15_the_allocator_contract_on_the_brotli_shape() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_brotli_shape_full_solve_under_the_contract",
        &[
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", "on"),
            ("CRAT_ERA5C_ALLOCATOR_CONTRACT", "on"),
        ],
    );
    assert!(text.contains("E5C_CONTRACT_OK"), "{text}");
}

/// R412-12: with the contract pin OFF an indirect call's result is opaque
/// under the frame — never Owning by the objective alone.
#[test]
#[ignore = "runs under CRAT_ERA5C_MOVE_TRACKING=on, contract off, in a child of e5c_w16"]
fn e5c_inner_brotli_shape_indirect_result_is_opaque_without_the_contract() {
    assert!(super::null_paths::move_tracking());
    assert!(!super::allocator_contract::enabled());
    let rows = brotli_shape_model();
    let kind = |k: &str| {
        rows.iter()
            .find(|(key, _)| key == k)
            .map(|(_, v)| v.clone())
    };
    assert_ne!(
        kind("make::_4@d0").as_deref(),
        Some("owning"),
        "make::p {rows:?}"
    );
    assert_ne!(
        kind("wrong_free::_4@d0").as_deref(),
        Some("owning"),
        "wrong_free::q {rows:?}"
    );
    assert_ne!(
        kind("BrotliAllocate::_0@d0").as_deref(),
        Some("owning"),
        "{rows:?}"
    );
    eprintln!("E5C_OPAQUE_OK");
}

#[test]
fn e5c_w16_an_indirect_call_result_is_opaque_without_the_contract() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_brotli_shape_indirect_result_is_opaque_without_the_contract",
        &[
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", "on"),
            ("CRAT_ERA5C_ALLOCATOR_CONTRACT", "off"),
        ],
    );
    assert!(text.contains("E5C_OPAQUE_OK"), "{text}");
}

/// The default arm (no era-5c pin) is unchanged: the indirect call's result
/// still floats — recorded as the baseline gap R412-12 names, not endorsed.
#[test]
fn e5c_w17_the_default_arm_still_floats_an_indirect_result() {
    assert!(!super::null_paths::move_tracking() && !super::allocator_contract::enabled());
    let rows = brotli_shape_model();
    let kind = |k: &str| {
        rows.iter()
            .find(|(key, _)| key == k)
            .map(|(_, v)| v.clone())
    };
    assert_eq!(kind("make::_4@d0").as_deref(), Some("owning"), "{rows:?}");
}

// ---- era-5c report 043 / R536-4: a formal with no allocation site and no free
// is a LEND. At L01⁶ lever (b) preferred `own` on every local and dragged such
// formals to Owning through their copies, returns and loads. Two shapes, two
// controls. Inner tests print; the outer test runs them under L01⁶'s arms.

const W43_HEMAN: &str = r#"
#[repr(C)] pub struct V { pub x: f32, pub y: f32 }
#[no_mangle]
pub unsafe extern "C" fn add(p_out: *mut V, a: *const V, b: *const V) -> *mut V {
    (*p_out).x = (*a).x + (*b).x;
    (*p_out).y = (*a).y + (*b).y;
    p_out
}
#[no_mangle]
pub unsafe extern "C" fn mid(p_out: *mut V, a: *const V, b: *const V) -> *mut V {
    let mut s = V { x: 0., y: 0. };
    add(&mut s, a, b);
    (*p_out).x = s.x / 2.0;
    (*p_out).y = s.y / 2.0;
    p_out
}
"#;

const W43_TULIP: &str = r#"
pub unsafe extern "C" fn ind(size: i32, outputs: *const *mut f64) -> i32 {
    let mut output: *mut f64 = *outputs.offset(0);
    let mut i = 0;
    while i < size {
        *output = 1.0;
        output = output.offset(1);
        i += 1;
    }
    // ti_ao's closing assert: `output - outputs[0] == size`
    if output.offset_from(*outputs.offset(0) as *const f64) as i32 != size {
        return 1;
    }
    0
}
pub static TABLE: [Option<unsafe extern "C" fn(i32, *const *mut f64) -> i32>; 1] = [Some(ind)];
"#;

const W43_OWNER: &str = r#"
#[repr(C)] pub struct V { pub x: f32, pub y: f32 }
unsafe extern "C" { fn malloc(n: usize) -> *mut V; fn free(p: *mut V); }
pub unsafe fn make() -> *mut V { let p = malloc(8); (*p).x = 0.; p }
pub unsafe fn user() { let q = make(); (*q).y = 1.0; free(q); }
"#;

#[test]
#[ignore = "runs under L01⁶'s arms in a child of e5c_w43"]
fn e5c_inner_w43_lend_formals() {
    for (name, code) in [
        ("HEMAN", W43_HEMAN),
        ("TULIP", W43_TULIP),
        ("OWNER", W43_OWNER),
    ] {
        for (k, v) in shape_model(code) {
            eprintln!("E5C_W43 {name} {k} {v}");
        }
    }
}

/// W43 (report 043): the lend formals are never Owning under lever (b), and the
/// controls keep their kinds -- a formal WITH a caller stays `ref`, and a
/// genuine constructor owner stays `owning`.
#[test]
fn e5c_w43_lend_formals_are_never_owning() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_w43_lend_formals",
        &[
            ("CRAT_ERA5B_INTERFACE_OWN", "on"),
            ("CRAT_ERA5B_RETURN_PORT", "on"),
            ("CRAT_ERA5B_PASS", "joint"),
            ("CRAT_ERA5C_MOVE_TRACKING", "on"),
            ("CRAT_ERA5C_FIELD_MOVE", "on"),
            ("CRAT_ERA5C_LEAK_PARITY", "on"),
            ("CRAT_ERA5C_OWN_PREFER_LOCAL", "on"),
            ("CRAT_ERA5C_RESEAT_A1", "off"),
        ],
    );
    let kind = |name: &str, key: &str| -> String {
        text.lines()
            .find_map(|l| {
                l.strip_prefix(&format!("E5C_W43 {name} {key} "))
                    .map(|v| v.trim().to_owned())
            })
            .unwrap_or_else(|| panic!("no row {name} {key}:\n{text}"))
    };
    // the two shapes: never Owning
    assert_ne!(
        kind("HEMAN", "mid::_1@d0"),
        "owning",
        "heman shape: exported formal, no caller"
    );
    assert_ne!(
        kind("TULIP", "ind::_2@d0"),
        "owning",
        "tulip shape: table-only formal"
    );
    // controls
    assert_eq!(
        kind("HEMAN", "add::_1@d0"),
        "ref",
        "control: the same idiom WITH a caller"
    );
    assert_eq!(
        kind("OWNER", "make::_1@d0"),
        "owning",
        "control: a constructor's allocation stays Box"
    );
    assert_eq!(
        kind("OWNER", "user::_1@d0"),
        "owning",
        "control: the caller receiving it stays Box"
    );
}

// ---------------------------------------------------------------------------
// W47 (era-5c report 047, R545-1): a table's reborrow is unique only when a Ref
// level below it is written. `CRAT_ERA5C_MUT_MODEL=on` recomputes the replay's
// mutability facts per round, keeping Foster's load guard only where the LOADED
// level is not Raw and reading each local's OUTERMOST level.

const W47_TULIP_READONLY: &str = r#"
pub unsafe extern "C" fn ind(size: i32, outputs: *const *mut f64) -> i32 {
    let mut output: *mut f64 = *outputs.offset(0);
    let mut i = 0;
    while i < size {
        let _x = *output;
        output = output.offset(1);
        i += 1;
    }
    if output.offset_from(*outputs.offset(0) as *const f64) as i32 != size {
        return 1;
    }
    0
}
pub static TABLE: [Option<unsafe extern "C" fn(i32, *const *mut f64) -> i32>; 1] = [Some(ind)];
"#;

/// A Ref element (no cursor arithmetic) written while the table is re-read.
const W47_REF_ELEMENT: &str = r#"
pub unsafe extern "C" fn rr(t: *const *mut f64) -> f64 {
    let e: *mut f64 = *t.offset(0);
    *e = 1.0;
    let again: *mut f64 = *t.offset(0);
    *e += *again;
    *e
}
pub static TABLE: [Option<unsafe extern "C" fn(*const *mut f64) -> f64>; 1] = [Some(rr)];
"#;

const W47_ARMS: &[(&str, &str)] = &[
    ("CRAT_ERA5B_INTERFACE_OWN", "on"),
    ("CRAT_ERA5B_RETURN_PORT", "on"),
    ("CRAT_ERA5B_PASS", "joint"),
    ("CRAT_ERA5C_MOVE_TRACKING", "on"),
    ("CRAT_ERA5C_FIELD_MOVE", "on"),
    ("CRAT_ERA5C_LEAK_PARITY", "on"),
    ("CRAT_ERA5C_OWN_PREFER_LOCAL", "on"),
    ("CRAT_ERA5C_RESEAT_A1", "on"),
];

#[test]
#[ignore = "runs under L01⁸'s arms in a child of e5c_w47"]
fn e5c_inner_w47_tables() {
    for (name, code) in [
        ("TULIP", W43_TULIP),
        ("READONLY", W47_TULIP_READONLY),
        ("REFELEM", W47_REF_ELEMENT),
        ("HEMAN", W43_HEMAN),
        ("OWNER", W43_OWNER),
    ] {
        for (k, v) in shape_model(code) {
            eprintln!("E5C_W47 {name} {k} {v}");
        }
    }
}

fn w47_rows(extra: &[(&str, &str)]) -> std::collections::BTreeMap<String, String> {
    let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
    env.extend_from_slice(extra);
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_w47_tables",
        &env,
    );
    text.lines()
        .filter_map(|l| l.strip_prefix("E5C_W47 "))
        .filter_map(|l| {
            let mut it = l.splitn(3, ' ');
            Some((
                format!("{} {}", it.next()?, it.next()?),
                it.next()?.trim().to_owned(),
            ))
        })
        .collect()
}

fn w47_kind(rows: &std::collections::BTreeMap<String, String>, key: &str) -> String {
    rows.get(key)
        .cloned()
        .unwrap_or_else(|| panic!("no row {key}: {rows:?}"))
}

/// W47: the witness and its controls.
#[test]
fn e5c_w47_a_tables_reborrow_is_unique_only_under_a_written_ref_level() {
    let on = w47_rows(&[("CRAT_ERA5C_MUT_MODEL", "on")]);
    let off = w47_rows(&[("CRAT_ERA5C_MUT_MODEL", "off")]);
    // the witness: tulip's table keeps `ref` at depth 0
    assert_eq!(
        w47_kind(&on, "TULIP ind::_2@d0"),
        "ref",
        "W47: the outputs table at depth 0"
    );
    assert_eq!(
        w47_kind(&off, "TULIP ind::_2@d0"),
        "raw",
        "W47 is RED without the rule"
    );
    // control: the read-only variant is all-ref either way
    for rows in [&on, &off] {
        let readonly: Vec<_> = rows
            .iter()
            .filter(|(k, _)| k.starts_with("READONLY "))
            .collect();
        assert!(
            !readonly.is_empty() && readonly.iter().all(|(_, v)| *v == "ref"),
            "{readonly:?}"
        );
    }
    // control: a written Ref element still forbids the all-Ref model -- something is demoted
    assert!(
        on.iter()
            .any(|(k, v)| k.starts_with("REFELEM ") && v == "raw"),
        "the Ref-element shape must keep a demotion: {on:?}"
    );
    // control: W43's shapes are untouched by the rule
    for key in [
        "HEMAN mid::_1@d0",
        "HEMAN add::_1@d0",
        "OWNER make::_1@d0",
        "OWNER user::_1@d0",
    ] {
        assert_eq!(w47_kind(&on, key), w47_kind(&off, key), "{key}");
    }
    assert_eq!(w47_kind(&on, "HEMAN add::_1@d0"), "ref");
    assert_eq!(w47_kind(&on, "OWNER make::_1@d0"), "owning");
}

/// W47 faults: each one alone must turn the witness RED.
#[test]
fn e5c_w47_b_faults_turn_the_witness_red() {
    for fault in ["any-depth", "no-model"] {
        let rows = w47_rows(&[
            ("CRAT_ERA5C_MUT_MODEL", "on"),
            ("CRAT_E5C_W47_FAULT", fault),
        ]);
        assert_eq!(
            w47_kind(&rows, "TULIP ind::_2@d0"),
            "raw",
            "fault {fault} must be caught"
        );
    }
}

#[test]
#[ignore = "runs in a child of e5c_w47_c"]
fn e5c_inner_w47_rule_level() {
    use rustc_hir::{ItemKind, OwnerNode};
    ::utils::compilation::run_compiler_on_str(W47_REF_ELEMENT, |tcx| {
        let mut functions = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            if let ItemKind::Fn { .. } = item.kind {
                functions.push(item.owner_id.def_id);
            }
        }
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs: Vec::new(),
        };
        let slots = super::crate_slots::CrateSlots::build(&program);
        let rr = program.functions[0];
        let universe = &slots.fn_local_slots[&rr];
        let all = |kind| -> rustc_hash::FxHashMap<super::solver::SlotRef, super::SlotKind> {
            (0..universe.len())
                .map(|i| {
                    (
                        super::solver::SlotRef::Local(rr, super::slots::SlotId::from_usize(i)),
                        kind,
                    )
                })
                .collect()
        };
        let table = rustc_middle::mir::Local::from_u32(1);
        for (name, kind) in [
            ("all-ref", super::SlotKind::Ref),
            ("all-raw", super::SlotKind::Raw),
        ] {
            let facts = super::borrow_verify::round_mutability_facts(&program, &slots, &all(kind));
            eprintln!(
                "E5C_W47_RULE {name} table-mutable={}",
                facts.is_mutable(rr, table)
            );
        }
    })
    .expect("compile");
}

/// W47 rule-level control: a written Ref element keeps the table's reborrow
/// unique (E0502-exact); only a Raw loaded level makes it shared.
#[test]
fn e5c_w47_c_a_written_ref_element_keeps_the_table_unique() {
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_w47_rule_level",
        &[],
    );
    assert!(
        text.contains("E5C_W47_RULE all-ref table-mutable=true"),
        "{text}"
    );
    assert!(
        text.contains("E5C_W47_RULE all-raw table-mutable=false"),
        "{text}"
    );
}

// ---------------------------------------------------------------------------
// W48 (era-5c report 048, R541-3): lil's cache write died building whole
// `serde_json::Value`s of the licensing snapshot's `matched` / `value_origins`
// (report 042). The streamed writers must be byte-identical to the old path.

/// The byte proof over real frames: `CRAT_E5C_W48_FILES` lists extracted
/// `licensing` arrays (one per program). Per snapshot, the streamed bytes must
/// equal the old `to_writer(&to_value(..))` bytes AND the file's own bytes.
#[test]
#[ignore = "byte proof over extracted cache entries (era-5c report 048)"]
fn e5c_w48_streamed_licensing_writers_are_byte_identical() {
    use super::licensing::{matched::MatchedTransport, value_origins::ValueOrigins};
    // Only the fields under proof are kept; serde skips the rest while
    // streaming (libzahl's array is 2.2 GB).
    #[derive(serde::Deserialize)]
    struct Pick {
        matched: serde_json::Value,
        value_origins: serde_json::Value,
        metadata: serde_json::Value,
    }
    let files = std::env::var("CRAT_E5C_W48_FILES").expect("CRAT_E5C_W48_FILES");
    for path in files.split(':').filter(|p| !p.is_empty()) {
        let reader = std::io::BufReader::new(std::fs::File::open(path).expect("open"));
        let snapshots: Vec<Pick> = serde_json::from_reader(reader).expect("parse");
        for (n, snapshot) in snapshots.iter().enumerate() {
            let matched = &snapshot.matched;
            let expected = serde_json::to_vec(matched).unwrap();
            let typed: MatchedTransport = serde_json::from_value(matched.clone()).expect("matched");
            let old = serde_json::to_vec(&serde_json::to_value(&typed).unwrap()).unwrap();
            let mut new = Vec::new();
            typed.write_canonical(&mut new).unwrap();
            assert!(new == old && new == expected, "{path}#{n} matched differs");
            let origins = &snapshot.value_origins;
            let expected = serde_json::to_vec(origins).unwrap();
            let typed: ValueOrigins = serde_json::from_value(origins.clone()).expect("origins");
            let old = serde_json::to_vec(&serde_json::to_value(&typed).unwrap()).unwrap();
            let mut new = Vec::new();
            typed.write_canonical(&mut new).unwrap();
            assert!(
                new == old && new == expected,
                "{path}#{n} value_origins differs"
            );
            let origins_len = expected.len();
            let metadata = &snapshot.metadata;
            let expected = serde_json::to_vec(metadata).unwrap();
            let typed: super::licensing::snapshot::Metadata =
                serde_json::from_value(metadata.clone()).expect("metadata");
            let old = serde_json::to_vec(&serde_json::to_value(&typed).unwrap()).unwrap();
            let mut new = Vec::new();
            typed.write_canonical(&mut new).unwrap();
            assert!(new == old && new == expected, "{path}#{n} metadata differs");
            eprintln!(
                "E5C_W48 {path}#{n} matched={} value_origins={origins_len} metadata={} IDENTICAL",
                serde_json::to_vec(matched).unwrap().len(),
                expected.len()
            );
        }
    }
}

/// W48b: the same proof without any whole `Value` (for libzahl, whose old path
/// is itself the allocation lil dies of): the typed fields are streamed and
/// their bytes must stand verbatim in the file after the snapshot's key.
#[test]
#[ignore = "byte proof against the file's own bytes (era-5c report 048)"]
fn e5c_w48b_streamed_writers_reproduce_the_files_bytes() {
    use super::licensing::{matched::MatchedTransport, value_origins::ValueOrigins};
    #[derive(serde::Deserialize)]
    struct Pick {
        matched: MatchedTransport,
        value_origins: ValueOrigins,
        metadata: super::licensing::snapshot::Metadata,
    }
    fn stands_after(bytes: &[u8], key: &[u8], value: &[u8], then: u8) -> usize {
        let mut hits = 0;
        let mut at = 0;
        while let Some(i) = bytes[at..].windows(key.len()).position(|w| w == key) {
            let start = at + i + key.len();
            if bytes[start..].starts_with(value) && bytes.get(start + value.len()) == Some(&then) {
                hits += 1;
            }
            at = start;
        }
        hits
    }
    let files = std::env::var("CRAT_E5C_W48_FILES").expect("CRAT_E5C_W48_FILES");
    for path in files.split(':').filter(|p| !p.is_empty()) {
        let bytes = std::fs::read(path).expect("read");
        let snapshots: Vec<Pick> = serde_json::from_slice(&bytes).expect("parse");
        for (n, snapshot) in snapshots.iter().enumerate() {
            let mut matched = Vec::new();
            snapshot.matched.write_canonical(&mut matched).unwrap();
            let mut origins = Vec::new();
            snapshot
                .value_origins
                .write_canonical(&mut origins)
                .unwrap();
            let m = stands_after(&bytes, b"\"matched\":", &matched, b',');
            let o = stands_after(&bytes, b"\"value_origins\":", &origins, b'}');
            let mut metadata = Vec::new();
            snapshot.metadata.write_canonical(&mut metadata).unwrap();
            let d = stands_after(&bytes, b"\"metadata\":", &metadata, b',');
            assert!(
                m >= 1 && o >= 1 && d >= 1,
                "{path}#{n}: matched hits {m}, value_origins hits {o}, metadata hits {d}"
            );
            eprintln!(
                "E5C_W48B {path}#{n} matched={} value_origins={} metadata={} IN-FILE",
                matched.len(),
                origins.len(),
                metadata.len()
            );
        }
    }
}

// ---------------------------------------------------------------------------
// W49 (era-5c L01⁸, R545-2): a formal whose every closed-world actual is the
// address of a stack or interior place is a LEND and never `Owning`
// (`CRAT_ERA5C_LEND_FORMAL=on`). Report 041's `init65::_2`, reduced.

const W49_H65: &str = r#"
#[repr(C)] #[derive(Copy, Clone)] pub struct Common { pub extra: *mut u8, pub n: i32 }
#[repr(C)] #[derive(Copy, Clone)] pub struct Comp { pub hb_common: Common, pub extra: *mut u8, pub common: *mut Common, pub fresh: i32 }
#[repr(C)] pub struct Hasher { pub common: Common, pub privat: Comp }
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn init(common: *mut Common, self_0: *mut Comp) {
    (*self_0).common = common;
    (*self_0).extra = (*common).extra;
    (*self_0).hb_common = *(*self_0).common;
    (*self_0).fresh = 1;
}
unsafe fn read(self_0: *mut Comp) -> i32 { (*(*self_0).common).n }
#[no_mangle] pub unsafe extern "C" fn setup(hasher: *mut Hasher) -> i32 {
    if (*hasher).common.extra.is_null() { (*hasher).common.extra = malloc(16); }
    init(&mut (*hasher).common, &mut (*hasher).privat);
    read(&mut (*hasher).privat)
}
#[no_mangle] pub unsafe extern "C" fn destroy(hasher: *mut Hasher) { free((*hasher).common.extra); }
"#;

const W49_OWNER: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn consume(p: *mut u8) { *p = 1; free(p); }
#[no_mangle] pub unsafe extern "C" fn run() { let p = malloc(4); consume(p); }
"#;

/// `&mut (*s).x` with `x` the FIRST field: the same address as the allocation.
const W49_FIRST_FIELD: &str = r#"
#[repr(C)] pub struct S { pub x: *mut u8, pub y: i32 }
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn consume(p: *mut *mut u8) { free(*p); }
#[no_mangle] pub unsafe extern "C" fn run() {
    let s = malloc(16) as *mut S; (*s).x = malloc(4); consume(&mut (*s).x); free(s as *mut u8);
}
"#;

const W49_STACK: &str = r#"
#[repr(C)] pub struct S { pub x: i32 }
unsafe fn init(p: *mut S) { (*p).x = 1; }
#[no_mangle] pub unsafe extern "C" fn setup() -> i32 { let mut s = S { x: 0 }; init(&mut s); s.x }
"#;

fn w49_lends(code: &str) -> Vec<String> {
    use rustc_hir::{ItemKind, OwnerNode};
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let mut functions = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            if let ItemKind::Fn { .. } = item.kind {
                functions.push(item.owner_id.def_id);
            }
        }
        super::lend_formals(tcx, &functions)
            .into_iter()
            .map(|(f, l)| format!("{}::_{}", tcx.def_path_str(f.to_def_id()), l.as_u32()))
            .collect()
    })
    .expect("compile")
}

#[test]
#[ignore = "runs in a child of e5c_w49_a (the fault is an env var)"]
fn e5c_inner_w49_selection() {
    for (name, code) in [
        ("H65", W49_H65),
        ("OWNER", W49_OWNER),
        ("FIRST", W49_FIRST_FIELD),
        ("STACK", W49_STACK),
        ("TABLE", W43_TULIP),
    ] {
        eprintln!("E5C_W49_SEL {name} {:?}", w49_lends(code));
    }
}

/// W49 selection: the H65 lends are selected (`&mut (*hasher).privat`, field 1,
/// into `init` and `read`) and `init::_1` (`&mut (*hasher).common`, the FIRST
/// field) is not; a
/// consuming owner and a first-field address are never selected; a stack
/// address is. The fault (first-field exclusion dropped) must be caught.
#[test]
fn e5c_w49_a_lend_formals_are_selected_exactly() {
    let run = |fault: Option<&str>| {
        let env: Vec<(&str, &str)> = fault
            .map(|f| vec![("CRAT_E5C_W49_FAULT", f)])
            .unwrap_or_default();
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_w49_selection",
            &env,
        )
    };
    let text = run(None);
    // `read(&mut (*hasher).privat)` is the same field-1 lend as `init`'s
    assert!(
        text.contains(r#"E5C_W49_SEL H65 ["init::_2", "read::_1"]"#),
        "{text}"
    );
    assert!(text.contains("E5C_W49_SEL OWNER []"), "{text}");
    assert!(text.contains("E5C_W49_SEL FIRST []"), "{text}");
    assert!(text.contains(r#"E5C_W49_SEL STACK ["init::_1"]"#), "{text}");
    // `ind` sits in a static fn-pointer table: address-taken, never selected
    assert!(text.contains("E5C_W49_SEL TABLE []"), "{text}");
    let faulty = run(Some("first-field"));
    assert!(
        !faulty.contains("E5C_W49_SEL FIRST []"),
        "the first-field fault must be caught: {faulty}"
    );
}

#[test]
#[ignore = "runs under L01⁸'s arms in a child of e5c_w49_b"]
fn e5c_inner_w49_models() {
    // TABLE: a full solve over a program with a static fn-pointer table. The
    // selection's static scan once built CTFE MIR, which STEALS the static's
    // body; the solve then panicked reading it.
    for (name, code) in [("H65", W49_H65), ("OWNER", W49_OWNER), ("TABLE", W43_TULIP)] {
        for (k, v) in shape_model(code) {
            eprintln!("E5C_W49 {name} {k} {v}");
        }
    }
}

/// W49 model: `init::_2` is never Owning under the arm (RED without it); a
/// genuine consuming owner keeps its Box.
#[test]
fn e5c_w49_b_a_lend_formal_is_never_owning() {
    let rows = |lf: &str| {
        let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
        env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
        env.push(("CRAT_ERA5C_LEND_FORMAL", lf));
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_w49_models",
            &env,
        )
    };
    let kind = |text: &str, key: &str| -> String {
        text.lines()
            .find_map(|l| {
                l.strip_prefix(&format!("E5C_W49 {key} "))
                    .map(|v| v.trim().to_owned())
            })
            .unwrap_or_else(|| panic!("no row {key}:\n{text}"))
    };
    let on = rows("on");
    let off = rows("off");
    assert_ne!(
        kind(&on, "H65 init::_2@d0"),
        "owning",
        "W49: the lend formal"
    );
    assert_eq!(
        kind(&off, "H65 init::_2@d0"),
        "owning",
        "W49 is RED without the rule"
    );
    assert_eq!(
        kind(&on, "OWNER consume::_1@d0"),
        "owning",
        "control: a consuming owner"
    );
    assert_eq!(
        kind(&on, "TABLE ind::_2@d0"),
        "ref",
        "the static-table program solves (W47)"
    );
}

// ---------------------------------------------------------------------------
// W52 (era-5c L01⁹, R549-2 (i)): A12's production selector.

#[test]
#[ignore = "runs in a child of e5c_w52 (the selector is an env var)"]
fn e5c_inner_w52_selector() {
    let identity = super::model_cache::solver_identity(
        super::a5_overlap::A5Mode::PreciseReplay,
        Some(super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
    );
    eprintln!(
        "E5C_W52 mode={} copy_lend={}",
        super::construction::CopyLendMode::current().label(),
        identity
            .lines()
            .find_map(|l| l.strip_prefix("era5c_copy_lend="))
            .unwrap_or("missing")
    );
}

/// The selector: absent = off = Baseline; `on` = LendArm, and the identity says
/// so; any other value fails loud.
#[test]
fn e5c_w52_the_copy_lend_selector_defaults_off_and_reaches_the_arm() {
    let inner = "analyses::borrow_ownership::null_paths_tests::e5c_inner_w52_selector";
    let off = child(inner, &[]);
    assert!(
        off.contains("E5C_W52 mode=baseline copy_lend=false"),
        "{off}"
    );
    let explicit_off = child(inner, &[("CRAT_ERA5C_COPY_LEND", "off")]);
    assert!(
        explicit_off.contains("E5C_W52 mode=baseline copy_lend=false"),
        "{explicit_off}"
    );
    let on = child(inner, &[("CRAT_ERA5C_COPY_LEND", "on")]);
    assert!(on.contains("E5C_W52 mode=lend_arm copy_lend=true"), "{on}");
    let exe = std::env::current_exe().expect("current_exe");
    let bad = std::process::Command::new(exe)
        .args([
            inner,
            "--exact",
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("CRAT_ERA5C_COPY_LEND", "yes")
        .output()
        .expect("child");
    assert!(!bad.status.success(), "a bad selector value must fail loud");
}

const W52_LEND: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p = malloc(4); *p = 1;
    let q = p;
    let v = *q;
    free(p);
    v
}
"#;

/// An aliasing write through the source while the lend is live.
const W52_WRITE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p = malloc(4); *p = 1;
    let q = p;
    *p = 2;
    let v = *q;
    free(p);
    v
}
"#;

/// A `free` of the source while the lend is live.
const W52_FREE_LIVE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p = malloc(4); *p = 1;
    let q = p;
    free(p);
    *q
}
"#;

#[test]
#[ignore = "runs under L01⁸'s arms in a child of e5c_w52_b"]
fn e5c_inner_w52_frame_path() {
    for (name, code) in [
        ("LEND", W52_LEND),
        ("WRITE", W52_WRITE),
        ("FREE", W52_FREE_LIVE),
    ] {
        for (k, v) in shape_model(code) {
            eprintln!("E5C_W52 {name} {k} {v}");
        }
    }
}

/// W52 on the A5 frame path (`solve_bo_a5_config`, the corpus solve's path) under
/// L01⁸'s arms: with the selector on, the lend recovers the owner (R1: the source
/// owns, the destination is a Ref), and the replay refuses it under an aliasing
/// write or a free of the source while it is live.
#[test]
fn e5c_w52_b_the_lend_arm_on_the_frame_path() {
    let rows = |lend: &str, fault: Option<&str>| {
        let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
        env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
        env.push(("CRAT_ERA5C_COPY_LEND", lend));
        if let Some(fault) = fault {
            env.push(("CRAT_E5C_W52_FAULT", fault));
        }
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_w52_frame_path",
            &env,
        )
    };
    let kind = |text: &str, key: &str| -> String {
        text.lines()
            .find_map(|l| {
                l.strip_prefix(&format!("E5C_W52 {key} "))
                    .map(|v| v.trim().to_owned())
            })
            .unwrap_or_else(|| panic!("no row {key}:\n{text}"))
    };
    let on = rows("on", None);
    let off = rows("off", None);
    // the lend: source owns, destination Ref; RED without the arm
    assert_eq!(
        kind(&on, "LEND run::_1@d0"),
        "owning",
        "the source keeps its Box"
    );
    assert_eq!(
        kind(&on, "LEND run::_2@d0"),
        "ref",
        "the destination is the lend"
    );
    assert_eq!(
        kind(&off, "LEND run::_2@d0"),
        "raw",
        "W52 is RED without the arm"
    );
    // the refusals
    assert_ne!(
        kind(&on, "WRITE run::_2@d0"),
        "ref",
        "a write through the source refuses the lend"
    );
    assert_ne!(
        kind(&on, "FREE run::_2@d0"),
        "ref",
        "a free of the source refuses the lend"
    );
    // On these frame-path shapes the refusals do not need the typed loan: both
    // pairs are eligible and the lend reading is satisfiable in the hard universe
    // (W54), so the verify loop refuses them without it. The emission's own
    // mutation is carried by W52c.
}

/// W52c, the ruled mutation: suppress the lend's loan emission
/// (`CRAT_E5C_W52_FAULT=no-loan`, at `selected_copy_lends_for_round`) and A12's
/// end-to-end emission witness goes RED; without the fault it is GREEN.
#[test]
fn e5c_w52_c_suppressing_the_lend_loan_turns_the_emission_witness_red() {
    let witness = "bo_c1::run::copy_lend_phase1b_bo_c1_end_to_end_recovers_owner";
    let run = |fault: bool| {
        let exe = std::env::current_exe().expect("current_exe");
        let mut command = std::process::Command::new(exe);
        command.args([witness, "--exact", "--test-threads=1"]);
        if fault {
            command.env("CRAT_E5C_W52_FAULT", "no-loan");
        }
        command.output().expect("child").status.success()
    };
    assert!(run(false), "the emission witness is GREEN");
    assert!(!run(true), "the no-loan fault must turn it RED");
}

/// era-5b's return port: a copy of an owner that is then RETURNED. The lend
/// reading must not mint a licence the objective buys (C2/C3: a returned
/// destination escapes, so the pair is ineligible).
const W52_RETURN: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
unsafe fn make() -> *mut i32 {
    let p = malloc(4); *p = 1;
    let q = p;
    q
}
#[no_mangle] pub unsafe extern "C" fn run() -> i32 { let r = make(); *r }
"#;

/// Source retirement: the lend's last use precedes the source's consumption by a
/// LOCAL callee that frees it.
const W52_RETIRE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
unsafe fn consume(p: *mut i32) { free(p); }
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p = malloc(4); *p = 1;
    let q = p;
    let v = *q;
    consume(p);
    v
}
"#;

#[test]
#[ignore = "runs under L01⁸'s arms in a child of e5c_w52_d"]
fn e5c_inner_w52_composition() {
    let bst = std::fs::read_to_string(BST).expect("bst corpus source");
    let delete = format!("{DECLS}{DELETE_SHAPE}");
    for (name, code) in [
        ("BST_CORPUS", bst.as_str()),
        ("DELETE", delete.as_str()),
        ("BST", BST_SHAPE),
        ("BST_LEAK", BST_LEAK_SHAPE),
        ("AVL", AVL_SHAPE),
        ("AVL_FREE", AVL_WITH_FREE_SHAPE),
        ("BROTLI", BROTLI_SHAPE),
        ("HEMAN", W43_HEMAN),
        ("TULIP", W43_TULIP),
        ("OWNER", W43_OWNER),
        ("READONLY", W47_TULIP_READONLY),
        ("REFELEM", W47_REF_ELEMENT),
        ("H65", W49_H65),
        ("W49_OWNER", W49_OWNER),
        ("FIRST", W49_FIRST_FIELD),
        ("STACK", W49_STACK),
        ("LEND", W52_LEND),
        ("WRITE", W52_WRITE),
        ("FREE", W52_FREE_LIVE),
        ("RETURN", W52_RETURN),
        ("RETIRE", W52_RETIRE),
    ] {
        for (k, v) in shape_model(code) {
            eprintln!("E5C_W52D {name} {k} {v}");
        }
    }
}

/// W52d, composition: every era-5c fixture (move tracking and null-joins, field
/// move, the traversal licence, lever (b), the lend formals, the mutability rule)
/// solved on the frame path under L01⁸'s arms with the copy-lend arm off and on.
/// The arm may turn Raw into Ref or Owning; it must never lose a Ref or an Owning.
/// Run twice: with the lend-formal arm off (L01⁸/L01⁹) and on.
#[test]
fn e5c_w52_d_the_lend_arm_loses_no_ref_and_no_owning_on_the_era5c_fixtures() {
    for lend_formal in ["off", "on"] {
        let rows = |copy_lend: &str| -> std::collections::BTreeMap<String, String> {
            let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
            env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
            env.push(("CRAT_ERA5C_LEND_FORMAL", lend_formal));
            env.push(("CRAT_ERA5C_COPY_LEND", copy_lend));
            let text = child(
                "analyses::borrow_ownership::null_paths_tests::e5c_inner_w52_composition",
                &env,
            );
            text.lines()
                .filter_map(|l| l.strip_prefix("E5C_W52D "))
                .filter_map(|l| l.rsplit_once(' '))
                .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
                .collect()
        };
        let off = rows("off");
        let on = rows("on");
        assert_eq!(off.len(), on.len(), "the same slots either way");
        let lost: Vec<_> = off
            .iter()
            .filter(|(k, v)| matches!(v.as_str(), "ref" | "owning") && on.get(*k) != Some(*v))
            .map(|(k, v)| format!("{k}: {v} -> {:?}", on.get(k)))
            .collect();
        let moved: Vec<_> = off
            .iter()
            .filter(|(k, v)| on.get(*k) != Some(*v))
            .map(|(k, v)| format!("{k}: {v} -> {:?}", on.get(k)))
            .collect();
        eprintln!("E5C_W52D_MOVED lend_formal={lend_formal} {moved:?}");
        assert!(
            lost.is_empty(),
            "lend_formal={lend_formal}: the arm lost {lost:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// W54 (era-5c R552-5, R549-2 (ii)): the A12 funnel S0 → S2 on the A5 frame.

/// Every copy pair's funnel row, keyed as the cache keys slots.
fn funnel_rows(code: &str) -> Vec<String> {
    use rustc_hir::{ItemKind, OwnerNode};
    let mut rows = Vec::new();
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = super::crate_slots::CrateSlots::build(&program);
        let origins = super::origins::compute_origins(&program);
        let mutability = super::mutability_facts::MutFacts::from_program(&program);
        let verdict = |v: Option<z3::SatResult>| match v {
            None => "na",
            Some(z3::SatResult::Sat) => "sat",
            Some(z3::SatResult::Unsat) => "unsat",
            Some(z3::SatResult::Unknown) => "unknown",
        };
        for row in super::construction::copy_lend_frame_funnel(
            &program,
            &slots,
            &origins,
            &mutability,
            std::time::Duration::from_secs(600),
        ) {
            let key = |local: rustc_middle::mir::Local| {
                super::slot_key::local_key(tcx, row.fn_did, local.as_usize(), 0)
            };
            rows.push(format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}",
                key(row.lhs_local),
                key(row.rhs_local),
                row.sites,
                row.drop.map_or("eligible", |drop| drop.label()),
                verdict(row.lend),
                verdict(row.source_own),
                row.shape,
            ));
        }
    });
    rows
}

/// The funnel over one named source file (`CRAT_E5C_SIDE_SOURCE`), rows to
/// `CRAT_E5C_FUNNEL_ROWS`: lhs, rhs, sites, S1 drop, S2 lend, source-own, shape.
#[test]
#[ignore = "the corpus funnel driver; runs under L01⁸'s arms + CRAT_ERA5C_COPY_LEND=on"]
fn e5c_funnel_named_source() {
    let path = std::env::var("CRAT_E5C_SIDE_SOURCE").expect("CRAT_E5C_SIDE_SOURCE");
    let source = std::fs::read_to_string(&path).expect("source");
    let rows = funnel_rows(&source);
    let out = std::env::var("CRAT_E5C_FUNNEL_ROWS").expect("CRAT_E5C_FUNNEL_ROWS");
    std::fs::write(&out, rows.join("\n") + "\n").expect("write funnel rows");
    eprintln!("E5C_FUNNEL {path} pairs={}", rows.len());
}

#[test]
#[ignore = "runs under L01⁸'s arms + the copy-lend arm in a child of e5c_w54"]
fn e5c_inner_w54_funnel() {
    for (name, code) in [
        ("LEND", W52_LEND),
        ("WRITE", W52_WRITE),
        ("FREE", W52_FREE_LIVE),
        ("RETURN", W52_RETURN),
        ("RETIRE", W52_RETIRE),
    ] {
        for row in funnel_rows(code) {
            eprintln!("E5C_W54 {name} {row}");
        }
    }
}

/// W54: the funnel's stages and shapes on the W52 fixtures. LEND and RETIRE are
/// eligible with the lend reading satisfiable, the first a `free` shape and the
/// second a local-callee shape; RETURN is dropped at S1 (C3). WRITE and FREE pass
/// S2 too: S2 is the hard universe, and W52b's refusals of both come later, in
/// the verify loop, so S2 is a ceiling on what the arm can realize.
#[test]
fn e5c_w54_the_funnel_reads_the_w52_fixtures() {
    let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
    env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
    env.push(("CRAT_ERA5C_COPY_LEND", "on"));
    let text = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_w54_funnel",
        &env,
    );
    let rows = |name: &str| -> Vec<Vec<String>> {
        text.lines()
            .filter_map(|l| l.strip_prefix(&format!("E5C_W54 {name} ")))
            .map(|l| l.split('\t').map(str::to_owned).collect())
            .collect()
    };
    eprintln!(
        "{}",
        text.lines()
            .filter(|l| l.starts_with("E5C_W54"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    let pair = |name: &str, lhs: &str| -> Vec<String> {
        rows(name)
            .into_iter()
            .find(|r| r[0].ends_with(lhs))
            .unwrap_or_else(|| panic!("{name}: no pair into {lhs}:\n{text}"))
    };
    let lend = pair("LEND", "run::_2@d0");
    assert_eq!(
        &lend[1..],
        ["run::_1@d0", "1", "eligible", "sat", "sat", "free"].map(String::from)
    );
    let retire = pair("RETIRE", "run::_2@d0");
    assert_eq!(retire[3], "eligible");
    assert_eq!(retire[4], "sat");
    assert_eq!(retire[6], "local-callee");
    for name in ["WRITE", "FREE"] {
        let row = pair(name, "run::_2@d0");
        assert_eq!(
            (row[3].as_str(), row[4].as_str()),
            ("eligible", "sat"),
            "{name}"
        );
    }
    assert!(
        rows("RETURN").iter().all(|r| r[3] != "eligible"),
        "a returned copy is never eligible"
    );
}

/// A4 (R560): the wall probe over one named source (`CRAT_E5C_SIDE_SOURCE`). The
/// targets are the keys in `CRAT_E5C_A4_TARGETS` (one per line); the accepted
/// kinds to hold come from the cache entry's model (`CRAT_E5C_A4_MODEL`, a JSON
/// object key -> kind). Rows to `CRAT_E5C_A4_ROWS`.
#[test]
#[ignore = "the A4 wall probe driver; runs under L01⁸'s arms"]
fn e5c_a4_wall_probe_named_source() {
    use rustc_hir::{ItemKind, OwnerNode};
    let path = std::env::var("CRAT_E5C_SIDE_SOURCE").expect("CRAT_E5C_SIDE_SOURCE");
    let source = std::fs::read_to_string(&path).expect("source");
    let wanted: Vec<String> =
        std::fs::read_to_string(std::env::var("CRAT_E5C_A4_TARGETS").expect("CRAT_E5C_A4_TARGETS"))
            .expect("targets")
            .lines()
            .map(str::to_owned)
            .filter(|l| !l.is_empty())
            .collect();
    let model: std::collections::BTreeMap<String, String> = serde_json::from_str(
        &std::fs::read_to_string(std::env::var("CRAT_E5C_A4_MODEL").expect("CRAT_E5C_A4_MODEL"))
            .expect("model"),
    )
    .expect("model json");
    let mut rows = Vec::new();
    let mut names: Vec<(String, String)> = Vec::new();
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = super::crate_slots::CrateSlots::build(&program);
        let origins = super::origins::compute_origins(&program);
        let mutability = super::mutability_facts::MutFacts::from_program(&program);
        let mut keyed = Vec::new();
        for (function, universe) in &slots.fn_local_slots {
            for index in 0..universe.len() {
                let id = super::slots::SlotId::from_usize(index);
                let s = universe.slot(id);
                let super::slots::SlotOwner::Local(local) = s.owner else { continue };
                keyed.push((
                    super::slot_key::local_key(tcx, *function, local.as_usize(), s.depth),
                    super::SlotRef::Local(*function, id),
                ));
            }
        }
        for index in 0..slots.field_slots.len() {
            let id = super::slots::SlotId::from_usize(index);
            let s = slots.field_slots.slot(id);
            let super::slots::SlotOwner::Field(field) = s.owner else { continue };
            keyed.push((
                super::slot_key::field_key(tcx, field.struct_did, field.field_index, s.depth),
                super::SlotRef::Field(id),
            ));
        }
        let targets: Vec<_> = wanted
            .iter()
            .map(|w| {
                keyed
                    .iter()
                    .find(|(k, _)| k == w)
                    .cloned()
                    .unwrap_or_else(|| panic!("no slot keyed {w}"))
            })
            .collect();
        let holds: Vec<_> = keyed
            .iter()
            .filter_map(|(k, s)| match model.get(k).map(String::as_str) {
                Some("ref") => Some((k.clone(), *s, false)),
                Some("owning") => Some((k.clone(), *s, true)),
                _ => None,
            })
            .collect();
        names = keyed
            .iter()
            .map(|(k, s)| (format!("{s:?}"), k.clone()))
            .collect();
        rows = super::construction::a4_wall_probe(
            &program,
            &slots,
            &origins,
            &mutability,
            &targets,
            &holds,
            std::time::Duration::from_secs(600),
        );
    });
    let out = std::env::var("CRAT_E5C_A4_ROWS").expect("CRAT_E5C_A4_ROWS");
    let mut names = names;
    names.sort_by_key(|(debug, _)| std::cmp::Reverse(debug.len()));
    let rows: Vec<String> = rows
        .into_iter()
        .map(|row| {
            names
                .iter()
                .fold(row, |row, (debug, key)| row.replace(debug.as_str(), key))
        })
        .collect();
    std::fs::write(&out, rows.join("\n") + "\n").expect("write a4 rows");
    eprintln!("E5C_A4 {path} rows={}", rows.len());
}

// ---------------------------------------------------------------------------
// W55 (era-5c L01⁹ rule 1b, R563-1): a deref-only field read is a Ref reader.

/// avl's `insert` shape: `(*(*node).left).key` reads through a CopyForDeref
/// temporary that the equate made Owning with the field and the exit then
/// finalized non-owning (era-5c 055, avl's `insert::_73`-`_76`).
const W55_INSERT: &str = r#"
#[repr(C)] pub struct Node { pub key: i32, pub left: *mut Node }
unsafe extern "C" { fn malloc(n: usize) -> *mut Node; fn free(p: *mut Node); }
unsafe fn newnode() -> *mut Node { let n = malloc(16); (*n).key = 0; (*n).left = 0 as *mut Node; n }
#[no_mangle] pub unsafe extern "C" fn insert(node: *mut Node) -> *mut Node {
    if node.is_null() { return newnode(); }
    (*node).left = insert((*node).left);
    if (*(*node).left).key > 0 { (*node).key = 1; }
    node
}
#[no_mangle] pub unsafe extern "C" fn destroy(a: *mut Node) { if !a.is_null() { destroy((*a).left); free(a); } }
#[no_mangle] pub unsafe extern "C" fn run() { let mut t = 0 as *mut Node; t = insert(t); t = insert(t); destroy(t); }
"#;

/// Control: the deref temporary of an uncalled reader already owns with the
/// field; the rule must not move it.
const W55_READER: &str = r#"
#[repr(C)] pub struct Node { pub key: i32, pub left: *mut Node }
unsafe extern "C" { fn malloc(n: usize) -> *mut Node; fn free(p: *mut Node); }
#[no_mangle] pub unsafe extern "C" fn leftkey(n: *mut Node) -> i32 { (*(*n).left).key }
#[no_mangle] pub unsafe extern "C" fn build() -> *mut Node {
    let a = malloc(16); let b = malloc(16);
    (*b).left = 0 as *mut Node; (*a).left = b; a
}
#[no_mangle] pub unsafe extern "C" fn destroy(a: *mut Node) { free((*a).left); free(a); }
"#;

#[test]
#[ignore = "runs under L01⁸'s arms in a child of e5c_w55"]
fn e5c_inner_w55() {
    for (name, code) in [("INSERT", W55_INSERT), ("READER", W55_READER)] {
        for (k, v) in shape_model(code) {
            eprintln!("E5C_W55 {name} {k} {v}");
        }
    }
}

fn w55_rows(extra: &[(&str, &str)]) -> std::collections::BTreeMap<String, String> {
    let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
    env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
    env.extend_from_slice(extra);
    child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_w55",
        &env,
    )
    .lines()
    .filter_map(|l| l.strip_prefix("E5C_W55 "))
    .filter_map(|l| l.rsplit_once(' '))
    .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
    .collect()
}

/// Diagnosis: the typed decline of a fixture (`CRAT_E5C_SHAPE` names it).
#[test]
#[ignore = "diagnosis only"]
fn e5c_inner_shape_decline_reason() {
    use rustc_hir::{ItemKind, OwnerNode};
    let code = match std::env::var("CRAT_E5C_SHAPE").as_deref() {
        Ok("AVL") => AVL_SHAPE,
        Ok("AVL_FREE") => AVL_WITH_FREE_SHAPE,
        other => panic!("unknown shape {other:?}"),
    };
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = super::crate_slots::CrateSlots::build(&program);
        let origins = super::origins::compute_origins(&program);
        let mutability = super::mutability_facts::MutFacts::from_program(&program);
        match super::construction::solve_bo_a5_config_reporting(
            &program,
            &slots,
            &origins,
            &mutability,
            super::a5_overlap::A5Mode::PreciseReplay,
            Some(super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ) {
            Ok(verified) => {
                eprintln!("E5C_DECLINE none");
                // W69e (R617-1): the receipt's repair stamp.
                for line in verified.receipt.lines() {
                    if line.starts_with("repair=") || line.starts_with("guarded_") {
                        eprintln!("E5C_REPAIR {line}");
                    }
                }
            }
            Err(decline) => eprintln!("E5C_DECLINE {decline:?}"),
        }
    })
    .unwrap();
}

/// W55a: with the arm the tree owns and the deref temporary is its Ref reader;
/// RED without the arm. W55b: the control does not move. W55c: the fault
/// (the full equate restored) turns W55a RED.
#[test]
fn e5c_w55_a_deref_only_reads_let_the_field_own() {
    let on = w55_rows(&[
        ("CRAT_ERA5C_DEREF_READER", "on"),
        ("CRAT_ERA5C_FIELD_OWN_REPAIR", "on"),
    ]);
    let off = w55_rows(&[("CRAT_ERA5C_DEREF_READER", "off")]);
    let fault = w55_rows(&[
        ("CRAT_ERA5C_DEREF_READER", "on"),
        ("CRAT_ERA5C_FIELD_OWN_REPAIR", "on"),
        ("CRAT_E5C_W55_FAULT", "equate"),
    ]);
    let kind = |rows: &std::collections::BTreeMap<String, String>, k: &str| {
        rows.get(k)
            .cloned()
            .unwrap_or_else(|| panic!("no row {k}: {rows:?}"))
    };
    assert_eq!(kind(&on, "INSERT Node::field1@d0"), "owning", "{on:?}");
    assert_eq!(
        kind(&on, "INSERT insert::_11@d0"),
        "ref",
        "the deref temporary reads"
    );
    assert_eq!(kind(&on, "INSERT insert::_1@d0"), "owning");
    assert_eq!(
        kind(&off, "INSERT Node::field1@d0"),
        "raw",
        "W55 is RED without the arm"
    );
    assert_eq!(
        kind(&fault, "INSERT Node::field1@d0"),
        "raw",
        "the fault must be caught"
    );
    let moved: Vec<_> = off
        .iter()
        .filter(|(k, v)| k.starts_with("READER ") && on.get(*k) != Some(*v))
        .collect();
    assert!(moved.is_empty(), "the control moved: {moved:?}");
}

/// W56: rule 1b's companion. Rule 1b opens avl's fields; the rotations then leave
/// a residual conflict on an Owning field, which declined the program. With
/// `CRAT_ERA5C_FIELD_OWN_REPAIR` the loop commits `¬own` on the field and accepts.
#[test]
fn e5c_w56_an_owning_field_residual_is_repaired_not_declined() {
    let reason = |repair: &str| -> String {
        let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
        env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
        env.push(("CRAT_ERA5C_DEREF_READER", "on"));
        env.push(("CRAT_ERA5C_FIELD_OWN_REPAIR", repair));
        env.push(("CRAT_E5C_SHAPE", "AVL"));
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_shape_decline_reason",
            &env,
        )
        .lines()
        .find_map(|l| l.strip_prefix("E5C_DECLINE ").map(str::to_owned))
        .expect("a decline line")
    };
    let off = reason("off");
    assert!(
        off.contains("field_kind=Some(Owning)"),
        "without the repair the Owning-field residual declines: {off}"
    );
    assert_eq!(
        reason("on"),
        "none",
        "with the repair the shape is accepted"
    );
}

/// W55d, composition: every era-5c fixture of W52d under L01⁸'s arms, the rule
/// off against on. Nothing Ref or Owning may fall to Raw, and nothing Owning may
/// become Ref; Ref -> Owning (an owner now moving through a temporary) is
/// reported, not refused.
#[test]
fn e5c_w55_d_the_rule_loses_no_ref_and_no_owning_on_the_era5c_fixtures() {
    let rows = |arm: &str| -> std::collections::BTreeMap<String, String> {
        let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
        env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
        // The L01⁹ rules built so far, together (1b, its repair, null-at-exit).
        env.push(("CRAT_ERA5C_DEREF_READER", arm));
        env.push(("CRAT_ERA5C_FIELD_OWN_REPAIR", arm));
        env.push(("CRAT_ERA5C_NULL_EXIT", arm));
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_w52_composition",
            &env,
        )
        .lines()
        .filter_map(|l| l.strip_prefix("E5C_W52D "))
        .filter_map(|l| l.rsplit_once(' '))
        .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
        .collect()
    };
    let off = rows("off");
    let on = rows("on");
    assert_eq!(off.len(), on.len(), "the same slots either way");
    let mut lost = Vec::new();
    let mut moved = Vec::new();
    for (k, v) in &off {
        let w = on.get(k).map(String::as_str).unwrap_or("?");
        if w == v {
            continue;
        }
        moved.push(format!("{k}: {v} -> {w}"));
        if (v != "raw" && w == "raw") || (v == "owning" && w == "ref") {
            lost.push(format!("{k}: {v} -> {w}"));
        }
    }
    eprintln!("E5C_W55D_MOVED {moved:?}");
    assert!(lost.is_empty(), "the rule lost {lost:?}");
}

// ---------------------------------------------------------------------------
// W57 (era-5c L01⁹, R563-1): a local null on every exit path is not finalized.

/// buffer's `test_buffer_slice__range_error` shape: `probe`'s `a` is tested and
/// the not-null branch aborts, so `a` is null at exit; its finalization pinned the
/// shared constructor's return, and so `user`'s owner, to non-owning.
const W57_NULL_EXIT: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); fn abort() -> !; }
unsafe fn make(ok: i32) -> *mut i32 { if ok == 0 { return 0 as *mut i32; } malloc(4) }
#[no_mangle] pub unsafe extern "C" fn probe() { let a = make(0); if a.is_null() {} else { abort(); } }
#[no_mangle] pub unsafe extern "C" fn user() -> i32 { let b = make(1); *b = 1; let v = *b; free(b); v }
"#;

/// Control: the not-null branch returns, so `a` may be live and non-null at exit
/// (a leak); the rule must not fire.
const W57_LEAK: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); fn abort() -> !; }
unsafe fn make(ok: i32) -> *mut i32 { if ok == 0 { return 0 as *mut i32; } malloc(4) }
#[no_mangle] pub unsafe extern "C" fn probe() { let a = make(0); if a.is_null() {} else { *a = 2; } }
#[no_mangle] pub unsafe extern "C" fn user() -> i32 { let b = make(1); *b = 1; let v = *b; free(b); v }
"#;

#[test]
#[ignore = "runs under L01⁸'s arms in a child of e5c_w57"]
fn e5c_inner_w57() {
    for (name, code) in [("NULL", W57_NULL_EXIT), ("LEAK", W57_LEAK)] {
        for (k, v) in shape_model(code) {
            eprintln!("E5C_W57 {name} {k} {v}");
        }
    }
}

/// W57: with the arm the constructor's return and `user`'s owner are Owning (RED
/// without); the leaking control stays raw; the fault (no divergence check) moves
/// the control and so is caught.
#[test]
fn e5c_w57_a_local_null_at_every_exit_is_not_finalized() {
    let rows = |extra: &[(&str, &str)]| -> std::collections::BTreeMap<String, String> {
        let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
        env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
        env.extend_from_slice(extra);
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_w57",
            &env,
        )
        .lines()
        .filter_map(|l| l.strip_prefix("E5C_W57 "))
        .filter_map(|l| l.rsplit_once(' '))
        .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
        .collect()
    };
    let on = rows(&[("CRAT_ERA5C_NULL_EXIT", "on")]);
    let off = rows(&[("CRAT_ERA5C_NULL_EXIT", "off")]);
    let fault = rows(&[
        ("CRAT_ERA5C_NULL_EXIT", "on"),
        ("CRAT_E5C_W57_FAULT", "no-diverge"),
    ]);
    for key in ["NULL make::_0@d0", "NULL user::_1@d0"] {
        assert_eq!(
            on.get(key).map(String::as_str),
            Some("owning"),
            "{key}: {on:?}"
        );
        assert_eq!(
            off.get(key).map(String::as_str),
            Some("raw"),
            "{key} is RED without the arm"
        );
    }
    assert_eq!(
        on.get("LEAK user::_1@d0").map(String::as_str),
        Some("raw"),
        "the control"
    );
    assert_ne!(
        fault.get("LEAK user::_1@d0").map(String::as_str),
        Some("raw"),
        "the no-diverge fault must move the control: {fault:?}"
    );
}

// ---------------------------------------------------------------------------
// W58 (era-5c L01⁹, R563-2 STOP 2): the narrow scope-exit close (addendum 101).

/// quadtree's `test_node` shape: a named local holding a fresh allocation from a
/// program constructor, never freed nor returned nor stored.
const W58_LEAK: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
unsafe fn make() -> *mut i32 { let p = malloc(4); p }
#[no_mangle] pub unsafe extern "C" fn leak() { let a = make(); *a = 2; }
#[no_mangle] pub unsafe extern "C" fn user() -> i32 { let b = make(); *b = 1; let v = *b; free(b); v }
"#;

/// Control: a call result that is a BORROWED pointer (a getter loads a field) is
/// not an allocation; its finalization stays.
const W58_GETTER: &str = r#"
#[repr(C)] pub struct Box2 { pub inner: *mut i32 }
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
unsafe fn getter(b: *mut Box2) -> *mut i32 { (*b).inner }
#[no_mangle] pub unsafe extern "C" fn peek(b: *mut Box2) { let a = getter(b); *a = 2; }
#[no_mangle] pub unsafe extern "C" fn user(b: *mut Box2) { let p = malloc(4); (*b).inner = p; }
#[no_mangle] pub unsafe extern "C" fn drop2(b: *mut Box2) { free((*b).inner); }
"#;

#[test]
#[ignore = "runs under L01⁸'s arms in a child of e5c_w58"]
fn e5c_inner_w58() {
    for (name, code) in [("LEAK", W58_LEAK), ("GETTER", W58_GETTER)] {
        for (k, v) in shape_model(code) {
            eprintln!("E5C_W58 {name} {k} {v}");
        }
    }
}

/// W58: with the arm the leaked constructor result and the freeing caller's owner
/// are Owning (RED without); the borrowed getter's result does not move; the
/// fault (any call result closed) is reported against the control.
#[test]
fn e5c_w58_a_fresh_call_result_live_at_exit_is_closed_not_finalized() {
    let rows = |extra: &[(&str, &str)]| -> std::collections::BTreeMap<String, String> {
        let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
        env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
        env.extend_from_slice(extra);
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_w58",
            &env,
        )
        .lines()
        .filter_map(|l| l.strip_prefix("E5C_W58 "))
        .filter_map(|l| l.rsplit_once(' '))
        .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
        .collect()
    };
    let on = rows(&[("CRAT_ERA5C_EXIT_CLOSE", "on")]);
    let off = rows(&[("CRAT_ERA5C_EXIT_CLOSE", "off")]);
    let fault = rows(&[
        ("CRAT_ERA5C_EXIT_CLOSE", "on"),
        ("CRAT_E5C_W58_FAULT", "any-call"),
    ]);
    for key in ["LEAK leak::_1@d0", "LEAK make::_0@d0", "LEAK user::_1@d0"] {
        assert_eq!(
            on.get(key).map(String::as_str),
            Some("owning"),
            "{key}: {on:?}"
        );
        assert_eq!(
            off.get(key).map(String::as_str),
            Some("raw"),
            "{key} is RED without the arm"
        );
    }
    let moved: Vec<_> = off
        .iter()
        .filter(|(k, v)| k.starts_with("GETTER ") && on.get(*k) != Some(*v))
        .collect();
    assert!(
        moved.is_empty(),
        "the borrowed getter's result moved: {moved:?}"
    );
    let faulted: Vec<_> = off
        .iter()
        .filter(|(k, v)| k.starts_with("GETTER ") && fault.get(*k) != Some(*v))
        .collect();
    eprintln!("E5C_W58_FAULT_MOVED {faulted:?}");
}

// ---------------------------------------------------------------------------
// W59 (era-5c L01⁹ rule 1a′, R565-3): store origins classified as a set.

/// Control: the stored value comes from an opaque foreign function -- an origin
/// the classification cannot name; it stays `Unknown`.
const W59_OPAQUE: &str = r#"
#![allow(dead_code, non_snake_case)]
#[repr(C)] pub struct Node { pub key: i32, pub left: *mut Node }
extern "C" { fn opaque() -> *mut Node; fn free(p: *mut Node); }
pub unsafe fn graft(n: *mut Node) { (*n).left = opaque(); }
pub unsafe fn prune(n: *mut Node) { free((*n).left); }
"#;

#[test]
#[ignore = "runs under L01⁸'s arms in a child of e5c_w59"]
fn e5c_inner_w59() {
    let name = std::env::var("CRAT_E5C_W59").expect("CRAT_E5C_W59");
    let code = match name.as_str() {
        "AVL" => AVL_SHAPE,
        "OPAQUE" => W59_OPAQUE,
        other => panic!("{other}"),
    };
    let _ = shape_model(code);
}

/// W59: on avl's insert-and-rotate shape, the recursive stores into `left` /
/// `right` classify as `All(..)` (the fields, the parameters) with the arm and as
/// `Unknown` without it; the opaque control stays `Unknown` either way.
#[test]
fn e5c_w59_store_origins_classify_as_a_set() {
    let lines = |shape: &str, arm: &str| -> Vec<String> {
        let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
        env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
        env.push(("CRAT_ERA5C_ORIGIN_SET", arm));
        env.push(("CRAT_R388_DEBUG", "1"));
        env.push(("CRAT_E5C_W59", shape));
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_w59",
            &env,
        )
        .lines()
        .filter(|l| l.starts_with("R388SET "))
        .map(str::to_owned)
        .collect()
    };
    let on = lines("AVL", "on");
    let off = lines("AVL", "off");
    let insert = |rows: &[String]| -> Vec<String> {
        rows.iter()
            .filter(|l| l.starts_with("R388SET insert "))
            .cloned()
            .collect()
    };
    assert!(
        !insert(&on).is_empty() && insert(&on).iter().all(|l| l.contains("-> All(")),
        "with the arm insert's stores classify as a set: {on:?}"
    );
    assert!(
        insert(&off).iter().any(|l| l.ends_with("-> Unknown")),
        "without the arm one is Unknown (RED): {off:?}"
    );
    for arm in ["on", "off"] {
        let control = lines("OPAQUE", arm);
        assert!(
            control.iter().all(|l| !l.contains("-> All(")),
            "an opaque origin is never classified ({arm}): {control:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// W60 (era-5c L01⁹ rule 2′, R568-4): a parameter moved into a field supports it.

/// P: `attach` moves its parameter `x` into `y.left`; a walker reads the field.
const W60_MOVED: &str = r#"
#[repr(C)] pub struct Node { pub key: i32, pub left: *mut Node }
unsafe extern "C" { fn malloc(n: usize) -> *mut Node; fn free(p: *mut Node); }
unsafe fn new() -> *mut Node { let n = malloc(16); (*n).key = 0; (*n).left = 0 as *mut Node; n }
unsafe fn attach(y: *mut Node, x: *mut Node) -> *mut Node { let t = x; (*y).left = t; y }
unsafe fn leftmost(n: *mut Node) -> *mut Node { let mut c = n; while !(*c).left.is_null() { c = (*c).left; } c }
unsafe fn destroy(n: *mut Node) { if !n.is_null() { destroy((*n).left); free(n); } }
#[no_mangle] pub unsafe extern "C" fn run() -> i32 { let t = attach(new(), new()); let m = leftmost(t); let k = (*m).key; destroy(t); k }
"#;

/// A (guarded): the parameter is stored and then freed by the callee.
const W60_FREED: &str = r#"
#[repr(C)] pub struct Node { pub key: i32, pub left: *mut Node }
unsafe extern "C" { fn malloc(n: usize) -> *mut Node; fn free(p: *mut Node); }
unsafe fn new() -> *mut Node { let n = malloc(16); (*n).key = 0; (*n).left = 0 as *mut Node; n }
unsafe fn attach(y: *mut Node, x: *mut Node) -> *mut Node { let t = x; (*y).left = t; free(x); (*y).left = 0 as *mut Node; y }
unsafe fn leftmost(n: *mut Node) -> *mut Node { let mut c = n; while !(*c).left.is_null() { c = (*c).left; } c }
unsafe fn destroy(n: *mut Node) { if !n.is_null() { destroy((*n).left); free(n); } }
#[no_mangle] pub unsafe extern "C" fn run() -> i32 { let t = attach(new(), new()); let m = leftmost(t); let k = (*m).key; destroy(t); k }
"#;

/// B (guarded): the parameter is stored and returned to a caller that frees it.
const W60_RETURNED: &str = r#"
#[repr(C)] pub struct Node { pub key: i32, pub left: *mut Node }
unsafe extern "C" { fn malloc(n: usize) -> *mut Node; fn free(p: *mut Node); }
unsafe fn new() -> *mut Node { let n = malloc(16); (*n).key = 0; (*n).left = 0 as *mut Node; n }
unsafe fn attach(y: *mut Node, x: *mut Node) -> *mut Node { let t = x; (*y).left = t; x }
unsafe fn leftmost(n: *mut Node) -> *mut Node { let mut c = n; while !(*c).left.is_null() { c = (*c).left; } c }
unsafe fn destroy(n: *mut Node) { if !n.is_null() { destroy((*n).left); free(n); } }
#[no_mangle] pub unsafe extern "C" fn run() -> i32 { let a = new(); let r = attach(a, new()); let m = leftmost(a); let k = (*m).key; (*a).left = 0 as *mut Node; free(r); destroy(a); k }
"#;

#[test]
#[ignore = "runs under L01⁸'s arms in a child of e5c_w60"]
fn e5c_inner_w60() {
    for (name, code) in [("P", W60_MOVED), ("A", W60_FREED), ("B", W60_RETURNED)] {
        for (k, v) in shape_model(code) {
            eprintln!("E5C_W60 {name} {k} {v}");
        }
    }
}

/// W60: with 1a′ and 1b on either way, the moved-input arm licenses P's field
/// (raw without it: RED) and not the guarded A and B; the transfer predicate
/// admits `linear` and `equal` by move and refuses `equal` by copy (control).
#[test]
fn e5c_w60_a_parameter_moved_into_a_field_supports_it() {
    use super::licensing::field_support::moved_transfer;
    assert!(moved_transfer("linear", false) && moved_transfer("equal", true));
    assert!(
        !moved_transfer("equal", false),
        "a copied operand keeps its hold"
    );
    let rows = |moved: &str| -> std::collections::BTreeMap<String, String> {
        let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
        env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
        env.push(("CRAT_ERA5C_ORIGIN_SET", "on"));
        env.push(("CRAT_ERA5C_DEREF_READER", "on"));
        env.push(("CRAT_ERA5C_FIELD_OWN_REPAIR", "on"));
        env.push(("CRAT_ERA5C_MOVED_INPUT", moved));
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_w60",
            &env,
        )
        .lines()
        .filter_map(|l| l.strip_prefix("E5C_W60 "))
        .filter_map(|l| l.rsplit_once(' '))
        .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
        .collect()
    };
    let on = rows("on");
    let off = rows("off");
    let field = |rows: &std::collections::BTreeMap<String, String>, shape: &str| {
        rows.get(&format!("{shape} Node::field1@d0"))
            .cloned()
            .unwrap_or_default()
    };
    assert_eq!(field(&on, "P"), "owning", "{on:?}");
    assert_eq!(field(&off, "P"), "raw", "W60 is RED without the arm");
    assert_eq!(
        field(&on, "A"),
        "raw",
        "a parameter freed after the store is not licensed"
    );
    assert_eq!(
        field(&on, "B"),
        "raw",
        "a parameter returned to a freeing caller is not licensed"
    );
    let lost: Vec<_> = off
        .iter()
        .filter(|(k, v)| {
            v.as_str() != "raw"
                && on.get(*k) != Some(*v)
                && on.get(*k).map(String::as_str) == Some("raw")
        })
        .collect();
    assert!(lost.is_empty(), "the arm lost {lost:?}");
}

// ---------------------------------------------------------------------------
// W53 (era-5c L01⁹, R551: the spec lane's B2/B3/B4).

#[test]
#[ignore = "runs in a child of e5c_w53 (every switch is an env var)"]
fn e5c_inner_w53_identity() {
    let identity = super::model_cache::solver_identity(
        super::a5_overlap::A5Mode::PreciseReplay,
        Some(super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
    );
    eprintln!("E5C_W53 {}", identity.replace('\n', "|"));
}

/// B3 (a) + B2: each constraint-changing switch, each fault hook and each
/// diagnosis pin moves the identity (and so the configuration digest).
#[test]
fn e5c_w53_a_every_switch_moves_the_identity() {
    let identity = |env: &[(&str, &str)]| -> String {
        let text = child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_w53_identity",
            env,
        );
        text.lines()
            .find_map(|l| l.strip_prefix("E5C_W53 ").map(str::to_owned))
            .expect("identity line")
    };
    let base = identity(&[]);
    for (name, value) in [
        ("CRAT_ERA5B_PASS", "era5a"),
        ("CRAT_ERA5B_REPAIR", "on"),
        ("CRAT_ERA5B_RELAX_FRAME", "on"),
        ("CRAT_E5C_W47_FAULT", "any-depth"),
        ("CRAT_E5C_W49_FAULT", "first-field"),
        ("CRAT_E5C_W52_FAULT", "no-loan"),
        ("CRAT_ERA5C_MOVE_STORE", "on"),
        ("CRAT_E5C_W61_FAULT", "raw-too"),
        ("CRAT_ERA5C_DEBUG", "1"),
        ("CRAT_ERA5C_BYTEPROOF", "1"),
        ("CRAT_ERA5C_RESEAT_DUMP", "1"),
    ] {
        assert_ne!(
            identity(&[(name, value)]),
            base,
            "{name}={value} must move the identity"
        );
    }
    assert!(base.contains("era5b_pass=joint"), "{base}");
    assert!(base.contains("era5c_test_faults=|"), "{base}");
    assert!(base.contains("era5c_diagnostics=|"), "{base}");
}

/// B4: era-5c's four families are registered, so a family-tracked core names
/// them instead of an `unregistered::` head.
#[test]
fn e5c_w53_b_era5c_label_families_are_registered() {
    for (label, family) in [
        ("lend-formal-forbid(Local(x))", "lend-formal-forbid"),
        ("field-move-kind(a=>b)", "field-move-kind"),
        (
            "own-guarded-traversal-formal-zero(f)",
            "own-guarded-traversal-formal-zero",
        ),
        (
            "own-guarded-traversal-receiver-legacy(f)",
            "own-guarded-traversal-receiver-legacy",
        ),
    ] {
        assert_eq!(
            super::solver::core_label_family(label),
            Some(family),
            "{label}"
        );
    }
}

// ---------------------------------------------------------------------------
// W61 (era-5c L01⁹ wall 4, R573-5): the store-as-move protocol's model half
// (design record §3 as era-5c 060a filed it; witnesses M1–M7 of its §6).

/// M2: avl's rotations in the CORPUS order (ownership-fields 067's reconstruction).
const AVL_CORPUS_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct Node { pub key: i32, pub height: i32, pub left: *mut Node, pub right: *mut Node }
pub unsafe fn height(n: *mut Node) -> i32 { if n.is_null() { return 0; } return (*n).height; }
pub unsafe fn newNode(key: i32) -> *mut Node {
    let mut node = malloc(core::mem::size_of::<Node>() as u64) as *mut Node;
    (*node).key = key; (*node).left = 0 as *mut Node; (*node).right = 0 as *mut Node; (*node).height = 1;
    return node;
}
pub unsafe fn rightRotate(y: *mut Node) -> *mut Node {
    let x = (*y).left;
    let T2 = (*x).right;
    (*y).left = T2;
    (*y).height = height((*y).left) + 1;
    (*x).right = y;
    (*x).height = height((*x).left) + 1;
    return x;
}
pub unsafe fn leftRotate(x: *mut Node) -> *mut Node {
    let y = (*x).right;
    let T2 = (*y).left;
    (*x).right = T2;
    (*x).height = height((*x).left) + 1;
    (*y).left = x;
    (*y).height = height((*y).left) + 1;
    return y;
}
pub unsafe fn insert(node: *mut Node, key: i32) -> *mut Node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key { (*node).left = insert((*node).left, key); }
    else { (*node).right = insert((*node).right, key); }
    if key < (*(*node).left).key { return rightRotate(node); }
    return leftRotate(node);
}
"#;

/// M4: the corpus order with a pointer derived from `y` before `(*x).right = y`
/// and written through after it.
const W61_DERIVED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct Node { pub key: i32, pub height: i32, pub left: *mut Node, pub right: *mut Node }
pub unsafe fn height(n: *mut Node) -> i32 { if n.is_null() { return 0; } return (*n).height; }
pub unsafe fn newNode(key: i32) -> *mut Node {
    let mut node = malloc(core::mem::size_of::<Node>() as u64) as *mut Node;
    (*node).key = key; (*node).left = 0 as *mut Node; (*node).right = 0 as *mut Node; (*node).height = 1;
    return node;
}
pub unsafe fn rightRotate(y: *mut Node) -> *mut Node {
    let x = (*y).left;
    let T2 = (*x).right;
    (*y).left = T2;
    (*y).height = height((*y).left) + 1;
    let h: *mut i32 = core::ptr::addr_of_mut!((*y).height);
    (*x).right = y;
    *h = *h + 0;
    (*x).height = height((*x).left) + 1;
    return x;
}
pub unsafe fn leftRotate(x: *mut Node) -> *mut Node {
    let y = (*x).right;
    let T2 = (*y).left;
    (*x).right = T2;
    (*x).height = height((*x).left) + 1;
    (*y).left = x;
    (*y).height = height((*y).left) + 1;
    return y;
}
pub unsafe fn insert(node: *mut Node, key: i32) -> *mut Node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key { (*node).left = insert((*node).left, key); }
    else { (*node).right = insert((*node).right, key); }
    if key < (*(*node).left).key { return rightRotate(node); }
    return leftRotate(node);
}
"#;

/// M6: as M4, with the derived pointer offset (raw evidence).
const W61_DERIVED_RAW: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; }
#[repr(C)] pub struct Node { pub key: i32, pub height: i32, pub left: *mut Node, pub right: *mut Node }
pub unsafe fn height(n: *mut Node) -> i32 { if n.is_null() { return 0; } return (*n).height; }
pub unsafe fn newNode(key: i32) -> *mut Node {
    let mut node = malloc(core::mem::size_of::<Node>() as u64) as *mut Node;
    (*node).key = key; (*node).left = 0 as *mut Node; (*node).right = 0 as *mut Node; (*node).height = 1;
    return node;
}
pub unsafe fn rightRotate(y: *mut Node) -> *mut Node {
    let x = (*y).left;
    let T2 = (*x).right;
    (*y).left = T2;
    (*y).height = height((*y).left) + 1;
    let h: *mut i32 = core::ptr::addr_of_mut!((*y).height).offset(0);
    (*x).right = y;
    *h = *h + 0;
    (*x).height = height((*x).left) + 1;
    return x;
}
pub unsafe fn leftRotate(x: *mut Node) -> *mut Node {
    let y = (*x).right;
    let T2 = (*y).left;
    (*x).right = T2;
    (*x).height = height((*x).left) + 1;
    (*y).left = x;
    (*y).height = height((*y).left) + 1;
    return y;
}
pub unsafe fn insert(node: *mut Node, key: i32) -> *mut Node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key { (*node).left = insert((*node).left, key); }
    else { (*node).right = insert((*node).right, key); }
    if key < (*(*node).left).key { return rightRotate(node); }
    return leftRotate(node);
}
"#;

/// The W61 child: solve each shape and print the result, the loans the arm
/// cleared (member kind, whether it would have been invalid), the obligations,
/// and on an accept the model.
#[test]
#[ignore = "runs under L01⁹'s arms in a child of the W61 witnesses"]
fn e5c_inner_w61() {
    use rustc_hir::{ItemKind, OwnerNode};
    let only = std::env::var("CRAT_E5C_W61_ONLY").ok();
    for (name, code) in [
        ("AVL", AVL_SHAPE),
        ("CORPUS", AVL_CORPUS_SHAPE),
        ("DERIVED", W61_DERIVED),
        ("DERIVED_RAW", W61_DERIVED_RAW),
    ] {
        if only.as_deref().is_some_and(|only| only != name) {
            continue;
        }
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let mut functions = Vec::new();
            let mut structs = Vec::new();
            for owner in tcx.hir_crate(()).owners.iter() {
                let Some(owner) = owner.as_owner() else {
                    continue;
                };
                let OwnerNode::Item(item) = owner.node() else {
                    continue;
                };
                match item.kind {
                    ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                    ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                    _ => {}
                }
            }
            let program = crate::utils::rustc::RustProgram {
                tcx,
                functions,
                structs,
            };
            let slots = super::crate_slots::CrateSlots::build(&program);
            let origins = super::origins::compute_origins(&program);
            let mutability = super::mutability_facts::MutFacts::from_program(&program);
            let (result, export) = super::export::with_bo_export(|| {
                super::construction::solve_bo_a5_config_reporting(
                    &program,
                    &slots,
                    &origins,
                    &mutability,
                    super::a5_overlap::A5Mode::PreciseReplay,
                    Some(super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
                )
            });
            if let Some(rows) = &export.move_store_obligations {
                eprintln!(
                    "E5C_W61 {name} export rows={} uses={}",
                    rows.len(),
                    rows.iter().map(|r| r.uses.len()).sum::<usize>()
                );
            }
            let (removed, obligations) = super::move_store::last_round();
            for (function, rows) in &removed {
                for r in rows {
                    eprintln!(
                        "E5C_W61 {name} removed {} {:?} {:?} {:?} {}",
                        tcx.def_path_str(*function),
                        r.location,
                        r.borrowed,
                        r.kind,
                        r.was_invalid
                    );
                }
            }
            for o in &obligations {
                eprintln!(
                    "E5C_W61 {name} obligation {} {:?} alias={:?} uses={}",
                    tcx.def_path_str(o.function),
                    o.store,
                    o.alias,
                    o.uses.len()
                );
                for u in &o.kept_uses {
                    eprintln!(
                        "E5C_W61 {name} kept-use {} {:?} {:?} {:?} {} loan=kept",
                        tcx.def_path_str(o.function),
                        o.store,
                        u.location,
                        u.local,
                        u.kind.as_str()
                    );
                }
                for u in &o.uses {
                    eprintln!(
                        "E5C_W61 {name} use {} {:?} {:?} {:?} {} {}",
                        tcx.def_path_str(o.function),
                        o.store,
                        u.location,
                        u.local,
                        u.kind.as_str(),
                        u.dominated
                    );
                }
            }
            match result {
                Ok(verified) => {
                    eprintln!("E5C_W61 {name} result accepted");
                    for (slot, kind) in &verified.model {
                        let key = match slot {
                            super::SlotRef::Local(function, id) => {
                                let universe = &slots.fn_local_slots[function];
                                let s = universe.slot(*id);
                                let super::slots::SlotOwner::Local(local) = s.owner else {
                                    unreachable!()
                                };
                                super::slot_key::local_key(
                                    tcx,
                                    *function,
                                    local.as_usize(),
                                    s.depth,
                                )
                            }
                            super::SlotRef::Field(id) => {
                                let s = slots.field_slots.slot(*id);
                                let super::slots::SlotOwner::Field(field) = s.owner else {
                                    unreachable!()
                                };
                                super::slot_key::field_key(
                                    tcx,
                                    field.struct_did,
                                    field.field_index,
                                    s.depth,
                                )
                            }
                        };
                        eprintln!("E5C_W61 {name} kind {key} {kind:?}");
                    }
                }
                Err(decline) => eprintln!("E5C_W61 {name} result decline {decline:?}"),
            }
        })
        .unwrap();
    }
}

/// The W61 child's lines under the design record's arm set (W47 + `MUT_MODEL` +
/// 1b + 1a′ + 2′, `FIELD_OWN_REPAIR` off) plus `extra`.
fn w61_lines(extra: &[(&str, &str)]) -> Vec<String> {
    let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
    env.extend_from_slice(&[
        ("CRAT_ERA5C_MUT_MODEL", "on"),
        ("CRAT_ERA5C_ORIGIN_SET", "on"),
        ("CRAT_ERA5C_DEREF_READER", "on"),
        ("CRAT_ERA5C_MOVED_INPUT", "on"),
        ("CRAT_ERA5C_FIELD_OWN_REPAIR", "off"),
    ]);
    env.extend_from_slice(extra);
    child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_w61",
        &env,
    )
    .lines()
    .filter(|l| l.contains("E5C_W61 ") || l.starts_with("E5C move-store "))
    .map(|l| l[l.find("E5C").unwrap()..].to_owned())
    .collect()
}

fn w61_of<'a>(lines: &'a [String], shape: &str, what: &str) -> Vec<&'a str> {
    let prefix = format!("E5C_W61 {shape} {what} ");
    lines
        .iter()
        .filter_map(|l| l.strip_prefix(prefix.as_str()))
        .collect()
}

fn w61_accepted(lines: &[String], shape: &str) -> bool {
    lines
        .iter()
        .any(|l| l == &format!("E5C_W61 {shape} result accepted"))
}

fn w61_field_decline(lines: &[String], shape: &str) -> bool {
    w61_of(lines, shape, "result")
        .iter()
        .any(|l| l.contains("field_conflict=Some(Field(") && l.contains("field_kind=Some(Owning)"))
}

/// M1 + M3: `AVL_SHAPE` declines on the Owning field without the arm (RED) and is
/// accepted with it; every cleared loan is on a non-`Raw` local; the export
/// carries exactly `y`'s three uses after `(*x).right = y` in each rotation.
/// M3: an `equal` by copy is not a move (no fixture lowers a store that way
/// before optimisation, so the control is the predicate itself).
#[test]
fn e5c_w61_m1_avl_shape_stores_as_moves() {
    use super::licensing::field_support::moved_transfer;
    assert!(
        !moved_transfer("equal", false),
        "M3: a copied operand keeps its loans"
    );
    let off = w61_lines(&[("CRAT_ERA5C_MOVE_STORE", "off")]);
    let on = w61_lines(&[("CRAT_ERA5C_MOVE_STORE", "on")]);
    assert!(
        w61_field_decline(&off, "AVL"),
        "M1 is RED without the arm: {off:?}"
    );
    assert!(w61_accepted(&on, "AVL"), "{on:?}");
    let removed = w61_of(&on, "AVL", "removed");
    assert!(
        !removed.is_empty() && removed.iter().all(|r| r.contains("Some(Owning)")),
        "{removed:?}"
    );
    assert!(
        removed.iter().any(|r| r.ends_with(" true")),
        "the cleared loans include invalid ones"
    );
    let uses = w61_of(&on, "AVL", "use");
    assert_eq!(uses.len(), 6, "{uses:?}");
    assert_eq!(
        w61_of(&on, "AVL", "export"),
        ["rows=6 uses=6"],
        "the export surface carries them"
    );
    for rotation in ["leftRotate", "rightRotate"] {
        let mine: Vec<_> = uses
            .iter()
            .filter(|u| u.starts_with(&format!("{rotation} bb0[6] ")))
            .map(|u| u.split(' ').skip(2).collect::<Vec<_>>().join(" "))
            .collect();
        assert_eq!(
            mine,
            [
                "bb0[10] _1 write-deref true",
                "bb0[14] _1 load-field true",
                "bb1[1] _1 write-deref true"
            ],
            "{rotation}"
        );
    }
}

/// M2: the corpus order declines without the arm (RED) and is accepted with it,
/// with no obligation (every row `uses=0`), the fields `Owning` and nothing raw.
#[test]
fn e5c_w61_m2_corpus_order_has_no_obligation() {
    let off = w61_lines(&[("CRAT_ERA5C_MOVE_STORE", "off")]);
    let on = w61_lines(&[("CRAT_ERA5C_MOVE_STORE", "on")]);
    assert!(
        w61_field_decline(&off, "CORPUS"),
        "M2 is RED without the arm: {off:?}"
    );
    assert!(w61_accepted(&on, "CORPUS"), "{on:?}");
    let rows = w61_of(&on, "CORPUS", "obligation");
    assert_eq!(rows.len(), 6, "{rows:?}");
    assert!(rows.iter().all(|r| r.ends_with(" uses=0")), "{rows:?}");
    let kinds = w61_of(&on, "CORPUS", "kind");
    for field in ["Node::field2@d0 Owning", "Node::field3@d0 Owning"] {
        assert!(kinds.contains(&field), "{kinds:?}");
    }
    assert!(kinds.iter().all(|k| !k.ends_with(" Raw")), "{kinds:?}");
}

/// M4: a `Ref` pointer derived from `y` before `(*x).right = y` is exported with
/// its uses after the store; the model's own loan on it then demotes it, and the
/// shape ends where it ends without the arm.
#[test]
fn e5c_w61_m4_a_ref_derived_pointer_is_exported() {
    let on = w61_lines(&[("CRAT_ERA5C_MOVE_STORE", "on"), ("CRAT_ERA5C_DEBUG", "1")]);
    let exported: Vec<_> = on
        .iter()
        .filter(|l| {
            l.starts_with("E5C move-store obligation fn=rightRotate") && l.contains(" local=_8 ")
        })
        .collect();
    assert!(
        exported.iter().any(|l| l.contains("kind=write-deref")),
        "the derived pointer's write after the store is exported: {on:?}"
    );
    assert!(w61_field_decline(&on, "DERIVED"));
}

/// M5: suppressing the export removes M1's obligations (the rewriter's R1 is the
/// backstop's witness); the loans are still cleared.
#[test]
fn e5c_w61_m5_the_export_fault_empties_the_obligations() {
    let fault = w61_lines(&[
        ("CRAT_ERA5C_MOVE_STORE", "on"),
        ("CRAT_E5C_W61_FAULT", "no-export"),
    ]);
    assert!(w61_of(&fault, "AVL", "use").is_empty(), "{fault:?}");
    assert!(w61_of(&fault, "AVL", "obligation").is_empty());
    assert!(!w61_of(&fault, "AVL", "removed").is_empty());
}

/// M6 + M7: a non-`Ref` pointer derived from `y` (a field address, offset) keeps
/// its loans: the shape declines on the same Owning field with and without the
/// arm, and no cleared loan names it. M7: the fault that clears those loans too
/// accepts the shape, so M6 is RED under it.
#[test]
fn e5c_w61_m6_m7_a_non_ref_derived_pointer_keeps_its_loans() {
    let off = w61_lines(&[("CRAT_ERA5C_MOVE_STORE", "off")]);
    let on = w61_lines(&[("CRAT_ERA5C_MOVE_STORE", "on"), ("CRAT_ERA5C_DEBUG", "1")]);
    let fault = w61_lines(&[
        ("CRAT_ERA5C_MOVE_STORE", "on"),
        ("CRAT_E5C_W61_FAULT", "raw-too"),
    ]);
    for shape in ["DERIVED", "DERIVED_RAW"] {
        assert!(w61_field_decline(&off, shape), "{shape} off: {off:?}");
        assert!(
            w61_field_decline(&on, shape),
            "{shape} on: the kept loan still declines"
        );
        assert!(
            w61_accepted(&fault, shape),
            "M7: {shape} is accepted under the fault"
        );
    }
    assert!(
        on.iter()
            .any(|l| l.starts_with("E5C move-store qualify fn=rightRotate")
                && l.contains("kept={_8}")),
        "the field address is kept: {on:?}"
    );
    // 069's `loan=kept` rows: `h`'s two uses after `(*x).right = y` are exported, kept.
    let kept = w61_of(&on, "DERIVED_RAW", "kept-use");
    assert_eq!(
        kept.iter()
            .filter(|u| u.starts_with("rightRotate "))
            .count(),
        2,
        "{kept:?}"
    );
    // `_8` is rightRotate's field address (leftRotate's `_8` is its store temporary).
    let removed = w61_of(&on, "DERIVED_RAW", "removed");
    assert!(
        removed
            .iter()
            .filter(|r| r.starts_with("rightRotate "))
            .all(|r| !r.contains(" _8 ")),
        "{removed:?}"
    );
}

/// W61 no-loss: the era-5c fixtures under L01⁹'s rules (1b + repair, 1a′, 2′)
/// with the arm on and off. No Ref or Owning slot may fall to raw, and no
/// Owning slot to Ref; gains are reported.
#[test]
fn e5c_w61_n_the_arm_loses_no_ref_and_no_owning_on_the_era5c_fixtures() {
    let rows = |arm: &str| -> std::collections::BTreeMap<String, String> {
        let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
        env.extend_from_slice(&[
            ("CRAT_ERA5C_MUT_MODEL", "on"),
            ("CRAT_ERA5C_DEREF_READER", "on"),
            ("CRAT_ERA5C_FIELD_OWN_REPAIR", "on"),
            ("CRAT_ERA5C_ORIGIN_SET", "on"),
            ("CRAT_ERA5C_MOVED_INPUT", "on"),
            ("CRAT_ERA5C_MOVE_STORE", arm),
        ]);
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_w52_composition",
            &env,
        )
        .lines()
        .filter_map(|l| l.strip_prefix("E5C_W52D "))
        .filter_map(|l| l.rsplit_once(' '))
        .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
        .collect()
    };
    let off = rows("off");
    let on = rows("on");
    assert_eq!(off.len(), on.len(), "the same slots either way");
    let mut lost = Vec::new();
    let mut moved = Vec::new();
    for (k, v) in &off {
        let w = on.get(k).map(String::as_str).unwrap_or("?");
        if w == v {
            continue;
        }
        moved.push(format!("{k}: {v} -> {w}"));
        if (v != "raw" && w == "raw") || (v == "owning" && w == "ref") {
            lost.push(format!("{k}: {v} -> {w}"));
        }
    }
    eprintln!("E5C_W61N_MOVED {moved:?}");
    assert!(lost.is_empty(), "the arm lost {lost:?}");
}

// ---------------------------------------------------------------------------
// W62 (era-5c L01⁹ wall 4, R574-5 (iii)): the store-as-move obligations travel
// in the portable export (schema v2) and the cache entry, and a consumer that
// asks for them is refused when an export or entry does not carry them.

/// The W62 child: solve `AVL_SHAPE` under the environment's arms, then read the
/// rows back three ways (model, portable export, staged cache entry).
#[test]
#[ignore = "runs under L01⁹'s arms in a child of the W62 witnesses"]
fn e5c_inner_w62() {
    use rustc_hir::{ItemKind, OwnerNode};
    ::utils::compilation::run_compiler_on_str(AVL_SHAPE, |tcx| {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = super::crate_slots::CrateSlots::build(&program);
        let origins = super::origins::compute_origins(&program);
        let mutability = super::mutability_facts::MutFacts::from_program(&program);
        let mode = super::a5_overlap::A5Mode::PreciseReplay;
        let attestation = Some(super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph);
        let (verified, captured) = super::export::with_bo_export(|| {
            super::construction::solve_bo_a5_config_reporting(
                &program,
                &slots,
                &origins,
                &mutability,
                mode,
                attestation,
            )
            .expect("W62 needs an accepted model")
        });
        let model = super::portable_export::move_store_rows(&program, &slots, &captured)
            .expect("rows convert");
        let describe = |rows: &Result<Vec<super::portable_export::MoveStoreRow>, String>| match rows
        {
            Ok(rows) => format!(
                "ok:{}:{}",
                rows.len(),
                rows.iter().map(|r| r.uses.len()).sum::<usize>()
            ),
            Err(e) => format!("err:{e}"),
        };
        let packet = super::portable_export::collect(&program, &slots, &captured).unwrap();
        let decoded: super::portable_export::PortableExport =
            serde_json::from_str(&packet.canonical_json().unwrap()).unwrap();
        let portable = decoded.move_store_obligations();
        let inputs = super::model_cache::semantic_inputs(&program, mode, attestation).unwrap();
        let key = super::cache_contract::semantic_key(&inputs).unwrap();
        super::model_cache::prepare(
            &program,
            &slots,
            &origins,
            &verified,
            &captured,
            mode,
            attestation,
        );
        let entry = super::model_cache::prepared_move_store_obligations(&key);
        let mut v1 = decoded.clone();
        v1.schema = "era5a-portable-export-v1".into();
        v1.families
            .remove(&super::portable_export::ExportFamily::MoveStoreObligations);
        eprintln!(
            "E5C_W62 model {}",
            match &model {
                Some(rows) => describe(&Ok(rows.clone())),
                None => "none".into(),
            }
        );
        eprintln!("E5C_W62 portable {}", describe(&portable));
        eprintln!("E5C_W62 entry {}", describe(&entry));
        eprintln!(
            "E5C_W62 equal portable={} entry={}",
            model
                .as_ref()
                .is_some_and(|m| portable.as_ref().is_ok_and(|p| p == m)),
            model
                .as_ref()
                .is_some_and(|m| entry.as_ref().is_ok_and(|e| e == m))
        );
        eprintln!(
            "E5C_W62 v1 validate={} consumer={}",
            v1.validate().is_ok(),
            describe(&v1.move_store_obligations())
        );
        // R577-5: each row's `cleared` against the replay's own record of the
        // loans it removed at that store (the last pass).
        let (removed, obligations) = super::move_store::last_round();
        let rows = model.clone().unwrap_or_default();
        let kind = |k: super::SlotKind| match k {
            super::SlotKind::Raw => "raw",
            super::SlotKind::Ref => "ref",
            super::SlotKind::Owning => "owning",
        };
        let matches = rows.len() == obligations.len()
            && obligations.iter().all(|ob| {
                let function = tcx.def_path_str(ob.function.to_def_id());
                let Some(row) = rows.iter().find(|r| {
                    r.function == function
                        && r.store.block == ob.store.block.as_u32()
                        && r.store.statement == ob.store.statement_index
                }) else {
                    return false;
                };
                let mut expected: Vec<(u32, &str)> = removed
                    .get(&ob.function)
                    .into_iter()
                    .flatten()
                    .filter(|r| r.location == ob.store)
                    .filter_map(|r| r.kind.map(|k| (r.borrowed.as_u32(), kind(k))))
                    .collect();
                expected.sort();
                expected.dedup_by_key(|(local, _)| *local);
                let got: Vec<(u32, &str)> = row
                    .cleared
                    .iter()
                    .map(|c| (c.local, c.kind.as_str()))
                    .collect();
                got == expected
            });
        let members: Vec<_> = rows.iter().flat_map(|r| r.cleared.iter()).collect();
        eprintln!(
            "E5C_W62 cleared rows={} nonempty={} members={} owning={} ref={} raw={} kept={} matches-removed={}",
            rows.len(),
            rows.iter().filter(|r| !r.cleared.is_empty()).count(),
            members.len(),
            members.iter().filter(|c| c.kind == "owning").count(),
            members.iter().filter(|c| c.kind == "ref").count(),
            members.iter().filter(|c| c.kind == "raw").count(),
            rows.iter()
                .map(|r| r.cleared.iter().filter(|c| r.kept.contains(&c.local)).count())
                .sum::<usize>(),
            matches
        );
    })
    .unwrap();
}

fn w62_lines(extra: &[(&str, &str)]) -> Vec<String> {
    let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
    env.extend_from_slice(&[
        ("CRAT_ERA5C_MUT_MODEL", "on"),
        ("CRAT_ERA5C_ORIGIN_SET", "on"),
        ("CRAT_ERA5C_DEREF_READER", "on"),
        ("CRAT_ERA5C_MOVED_INPUT", "on"),
        ("CRAT_ERA5C_FIELD_OWN_REPAIR", "on"),
    ]);
    env.extend_from_slice(extra);
    child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_w62",
        &env,
    )
    .lines()
    .filter_map(|l| l.find("E5C_W62 ").map(|i| l[i + 8..].to_owned()))
    .collect()
}

/// W62a: with the arm, the rows round-trip: the portable export and a staged
/// cache entry (read back through the streamed validator) return exactly the
/// model's rows (6 uses on `AVL_SHAPE`). Under the `drop-rows` fault the round
/// trip loses them (RED).
#[test]
fn e5c_w62_a_the_rows_round_trip_through_the_export_and_the_entry() {
    let on = w62_lines(&[("CRAT_ERA5C_MOVE_STORE", "on")]);
    assert!(on.contains(&"model ok:6:6".to_owned()), "{on:?}");
    assert!(on.contains(&"portable ok:6:6".to_owned()), "{on:?}");
    assert!(on.contains(&"entry ok:6:6".to_owned()), "{on:?}");
    assert!(
        on.contains(&"equal portable=true entry=true".to_owned()),
        "{on:?}"
    );
    let fault = w62_lines(&[
        ("CRAT_ERA5C_MOVE_STORE", "on"),
        ("CRAT_E5C_W62_FAULT", "drop-rows"),
    ]);
    assert!(fault.contains(&"entry ok:0:0".to_owned()), "{fault:?}");
    assert!(
        fault.contains(&"equal portable=false entry=false".to_owned()),
        "W62a is RED under the fault: {fault:?}"
    );
}

/// W62b / W62c: a consumer that asks is refused when the rows are absent — the
/// arm off (typed `NotRecorded`, from the export and from the entry) and a v1
/// export (no family; its schema is refused before any row is read).
#[test]
fn e5c_w62_b_c_a_consumer_is_refused_without_the_rows() {
    let off = w62_lines(&[("CRAT_ERA5C_MOVE_STORE", "off")]);
    assert!(off.contains(&"model none".to_owned()), "{off:?}");
    for side in ["portable", "entry"] {
        assert!(
            off.iter()
                .any(|l| l.starts_with(&format!("{side} err:move-store obligations not recorded"))),
            "{side}: {off:?}"
        );
    }
    let on = w62_lines(&[("CRAT_ERA5C_MOVE_STORE", "on")]);
    let v1 = on.iter().find(|l| l.starts_with("v1 ")).expect("v1 line");
    assert!(
        v1.starts_with("v1 validate=false consumer=err:move-store obligations need"),
        "{v1}"
    );
}

/// W62d (R577-5): every row carries `cleared`, the members whose loans its
/// store removed, exactly as the replay's last pass removed them; none is
/// `Raw` (a `Raw` member keeps its loan) and none is `kept` (3.2). Under the
/// `drop-cleared` fault the rows lose them (RED).
#[test]
fn e5c_w62_d_each_row_carries_the_members_its_store_cleared() {
    let on = w62_lines(&[("CRAT_ERA5C_MOVE_STORE", "on")]);
    let cleared = on
        .iter()
        .find(|l| l.starts_with("cleared "))
        .expect("cleared line");
    assert!(
        cleared.contains(" raw=0 kept=0 matches-removed=true"),
        "{cleared}"
    );
    assert!(
        cleared.starts_with("cleared rows=6 nonempty=6 "),
        "{cleared}"
    );
    let fault = w62_lines(&[
        ("CRAT_ERA5C_MOVE_STORE", "on"),
        ("CRAT_E5C_W62_FAULT", "drop-cleared"),
    ]);
    let cleared = fault
        .iter()
        .find(|l| l.starts_with("cleared "))
        .expect("cleared line");
    assert!(
        cleared.ends_with("matches-removed=false"),
        "W62d is RED under the fault: {cleared}"
    );
}

/// era-5c 060 (R570-1 (b)): the supervisor's capped entry verifier. Streams one
/// cache entry (`CRAT_E5C_ENTRY`) through the worker's own reader --
/// `cache_contract::validate_file` then `canonical_file_hashes`, exactly the
/// worker's existing-entry path -- and prints its key and three digests.
#[test]
#[ignore = "the supervisor's capped entry verifier (era-5c 060)"]
fn e5c_entry_digests() {
    let path = std::path::PathBuf::from(std::env::var("CRAT_E5C_ENTRY").expect("CRAT_E5C_ENTRY"));
    let entry = super::cache_contract::validate_file(&path).expect("a valid cache entry");
    let hashes = entry
        .canonical_file_hashes(&path)
        .expect("streamed digests");
    println!(
        "E5C_ENTRY_DIGESTS {{\"key\":\"{}\",\"entry\":\"{}\",\"payload\":\"{}\",\"exports\":\"{}\"}}",
        entry.key, hashes.entry, hashes.payload, hashes.exports
    );
}

/// era-5c 066 (the lend, rule 5): the market as a MIR walk, no solver. For every
/// raw-pointer formal of a local function, the formal's derivation closure (copies,
/// casts, field and element addresses, `offset`-like library calls, interior-pointer
/// libc results) is followed through the body, and the formal is a CONSUMER if the
/// closure is freed, stored as a value (into memory or an aggregate), returned, or
/// handed to a consuming or unknown callee; otherwise it only reads or writes
/// THROUGH the pointer and is a PASS-THROUGH (lendable). Greatest fixpoint over the
/// local callees. `reader=` says whether era 5b's reader plan already certifies it.
/// `CRAT_E5C_LEND_INPUT` names one `lib.rs`; `CRAT_E5C_LEND_STRICT=1` treats every
/// libc callee as unknown.
#[test]
#[ignore = "era-5c 066: the lend's market as a MIR walk, no solver"]
fn e5c_lend_market() {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::mir::{Operand, Rvalue, StatementKind};

    use crate::analyses::mir::{CallKind, TerminatorExt};
    let path = std::env::var("CRAT_E5C_LEND_INPUT").expect("CRAT_E5C_LEND_INPUT");
    let strict = std::env::var("CRAT_E5C_LEND_STRICT").as_deref() == Ok("1");
    let source = std::fs::read_to_string(&path).expect("source");
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions: functions.clone(),
            structs,
        };
        let slots = super::crate_slots::CrateSlots::build(&program);
        let plan = super::licensing::readers::Plan::build(
            &super::licensing::readers::Inputs::collect(&program, &slots),
        );
        // libc callees that neither free nor retain a pointer argument (and the
        // ones whose result points into an argument).
        const NO_RETAIN: &[&str] = &[
            "strlen", "strcmp", "strncmp", "strcasecmp", "strncasecmp", "strcpy", "strncpy",
            "strcat", "strncat", "memcpy", "memmove", "memset", "memcmp", "printf", "fprintf",
            "sprintf", "snprintf", "vsnprintf", "vfprintf", "puts", "fputs", "fputc", "putc",
            "fwrite", "fread", "fgets", "fgetc", "getc", "sscanf", "fscanf", "atoi", "atol",
            "atof", "strtol", "strtoul", "strtod", "strtoll", "strtoull", "fflush", "ferror",
            "feof", "fseek", "ftell", "rewind", "strspn", "strcspn", "qsort", "bsearch",
        ];
        const INTERIOR: &[&str] = &["strchr", "strrchr", "strstr", "strpbrk", "memchr"];
        let name = |f: rustc_span::def_id::LocalDefId| tcx.def_path_str(f.to_def_id());
        let pointer_formals = |f: rustc_span::def_id::LocalDefId| -> Vec<rustc_middle::mir::Local> {
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            (1..=body.arg_count)
                .map(rustc_middle::mir::Local::from_usize)
                .filter(|&l| body.local_decls[l].ty.is_raw_ptr())
                .collect()
        };
        let mut consumer: std::collections::BTreeMap<(String, u32), String> = Default::default();
        loop {
            let before = consumer.len();
            for &f in &functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                for formal in pointer_formals(f) {
                    let key = (name(f), formal.as_u32());
                    if consumer.contains_key(&key) {
                        continue;
                    }
                    // The derivation closure, to a fixpoint.
                    let mut closure = std::collections::BTreeSet::from([formal]);
                    let in_closure = |op: &Operand<'_>, c: &std::collections::BTreeSet<_>| {
                        op.place()
                            .is_some_and(|p| p.projection.is_empty() && c.contains(&p.local))
                    };
                    let mut reason: Option<String> = None;
                    loop {
                        let size = closure.len();
                        for data in body.basic_blocks.iter() {
                            for statement in &data.statements {
                                let StatementKind::Assign(assign) = &statement.kind else {
                                    continue;
                                };
                                let (dest, rvalue) = &**assign;
                                let derived = match rvalue {
                                    Rvalue::Use(op) | Rvalue::Cast(_, op, _) => {
                                        in_closure(op, &closure)
                                    }
                                    Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place) => {
                                        place.is_indirect_first_projection()
                                            && closure.contains(&place.local)
                                    }
                                    _ => false,
                                };
                                if derived {
                                    if dest.projection.is_empty() {
                                        if dest.local.as_u32() == 0 {
                                            reason.get_or_insert("return".into());
                                        } else {
                                            closure.insert(dest.local);
                                        }
                                    } else {
                                        reason.get_or_insert("store".into());
                                    }
                                }
                                if let Rvalue::Aggregate(_, ops) = rvalue
                                    && ops.iter().any(|op| in_closure(op, &closure))
                                {
                                    reason.get_or_insert("aggregate".into());
                                }
                            }
                            let Some(call) = data.terminator().as_call(tcx) else { continue };
                            let hits: Vec<usize> = call
                                .args
                                .iter()
                                .enumerate()
                                .filter(|(_, a)| in_closure(&a.node, &closure))
                                .map(|(i, _)| i)
                                .collect();
                            if hits.is_empty() {
                                continue;
                            }
                            let mut derives = false;
                            match &call.func {
                                CallKind::FreeStanding(g) | CallKind::Impl(g) => {
                                    let gbody = tcx.mir_drops_elaborated_and_const_checked(*g).borrow();
                                    for &i in &hits {
                                        let k = (name(*g), (i + 1) as u32);
                                        let is_ptr = i < gbody.arg_count
                                            && gbody.local_decls[rustc_middle::mir::Local::from_usize(i + 1)]
                                                .ty
                                                .is_raw_ptr();
                                        if !is_ptr {
                                            reason.get_or_insert(format!("callee-nonpointer:{}#{}", k.0, k.1));
                                        } else if consumer.contains_key(&k) {
                                            reason.get_or_insert(format!("consuming-callee:{}#{}", k.0, k.1));
                                        }
                                    }
                                }
                                CallKind::LibC(sym) => {
                                    let s = sym.as_str();
                                    if s == "free" || s == "realloc" {
                                        reason.get_or_insert(format!("frees:{s}"));
                                    } else if !strict && INTERIOR.contains(&s) {
                                        derives = true;
                                    } else if strict || !NO_RETAIN.contains(&s) {
                                        reason.get_or_insert(format!("unknown-libc:{s}"));
                                    }
                                }
                                CallKind::RustLib(did) => {
                                    let s = tcx.item_name(*did);
                                    let s = s.as_str();
                                    if matches!(
                                        s,
                                        "offset" | "add" | "sub" | "wrapping_offset" | "wrapping_add"
                                            | "wrapping_sub" | "cast" | "cast_mut" | "cast_const"
                                            | "as_ptr" | "as_mut_ptr"
                                    ) {
                                        derives = true;
                                    } else if !matches!(
                                        s,
                                        "is_null" | "offset_from" | "addr" | "eq" | "ne"
                                            // an `Option` field read in place (a callback
                                            // slot's test): the object is read, not handed on
                                            | "is_some" | "is_none" | "expect" | "unwrap"
                                    ) {
                                        reason.get_or_insert(format!("rust-lib:{s}"));
                                    }
                                }
                                CallKind::Closure | CallKind::Dynamic => {
                                    reason.get_or_insert("indirect".into());
                                }
                            }
                            if derives && call.destination.projection.is_empty() {
                                if call.destination.local.as_u32() == 0 {
                                    reason.get_or_insert("return".into());
                                } else {
                                    closure.insert(call.destination.local);
                                }
                            }
                        }
                        if closure.len() == size {
                            break;
                        }
                    }
                    if let Some(reason) = reason {
                        consumer.insert(key, reason);
                    }
                }
            }
            if consumer.len() == before {
                break;
            }
        }
        for &f in &functions {
            let fname = name(f);
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            for formal in pointer_formals(f) {
                let var = body
                    .var_debug_info
                    .iter()
                    .find_map(|info| match info.value {
                        rustc_middle::mir::VarDebugInfoContents::Place(p)
                            if p.local == formal && p.projection.is_empty() =>
                        {
                            Some(info.name.to_string())
                        }
                        _ => None,
                    })
                    .unwrap_or_default();
                let key = (fname.clone(), formal.as_u32());
                let reader = plan.borrows_parameter(&fname, formal.as_usize() - 1);
                match consumer.get(&key) {
                    Some(reason) => eprintln!(
                        "E5C_LEND {fname}::_{}@d0 {var} class=consumer reason={reason} reader={reader}",
                        formal.as_u32()
                    ),
                    None => eprintln!(
                        "E5C_LEND {fname}::_{}@d0 {var} class=pass-through reader={reader}",
                        formal.as_u32()
                    ),
                }
            }
        }
    })
    .unwrap();
}

/// W63 (era-5c 066, R579-2): lil's context shape (062's `ctx.rs`, verbatim): a
/// constructor, two readers of the context, a writer that pushes an
/// environment, a parse that drives them, and a null-checked free.
const W63_CTX: &str = r#"#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case, unused_mut)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; fn free(_: *mut core::ffi::c_void); }
#[repr(C)] pub struct env_t { pub parent: *mut env_t, pub depth: i32 }
#[repr(C)] pub struct ctx_t { pub code: *const u8, pub head: usize, pub clen: usize, pub ignoreeol: i32, pub env: *mut env_t }
pub type lil_t = *mut ctx_t;
#[no_mangle] pub unsafe extern "C" fn lil_new() -> lil_t {
    let mut lil = malloc(core::mem::size_of::<ctx_t>() as u64) as lil_t;
    (*lil).code = 0 as *const u8; (*lil).head = 0; (*lil).clen = 0; (*lil).ignoreeol = 0;
    (*lil).env = malloc(core::mem::size_of::<env_t>() as u64) as *mut env_t;
    (*(*lil).env).parent = 0 as *mut env_t; (*(*lil).env).depth = 0;
    return lil;
}
unsafe extern "C" fn ateol(mut lil: lil_t) -> i32 {
    return ((*lil).ignoreeol == 0 && *((*lil).code).offset((*lil).head as isize) == b'\n') as i32;
}
unsafe extern "C" fn skip_spaces(mut lil: lil_t) {
    while (*lil).head < (*lil).clen && *((*lil).code).offset((*lil).head as isize) == b' ' {
        if ateol(lil) != 0 { break; }
        (*lil).head = (*lil).head.wrapping_add(1);
    }
}
#[no_mangle] pub unsafe extern "C" fn lil_push_env(mut lil: lil_t) -> *mut env_t {
    let mut env = malloc(core::mem::size_of::<env_t>() as u64) as *mut env_t;
    (*env).parent = (*lil).env; (*env).depth = 1; (*lil).env = env;
    return env;
}
#[no_mangle] pub unsafe extern "C" fn lil_pop_env(mut lil: lil_t) {
    let mut env = (*lil).env;
    if !(*env).parent.is_null() { (*lil).env = (*env).parent; free(env as *mut core::ffi::c_void); }
}
#[no_mangle] pub unsafe extern "C" fn lil_parse(mut lil: lil_t, mut code: *const u8, mut len: usize) -> i32 {
    let save = (*lil).code; (*lil).code = code; (*lil).clen = len; (*lil).head = 0;
    lil_push_env(lil);
    skip_spaces(lil);
    let r = ateol(lil);
    lil_pop_env(lil);
    (*lil).code = save;
    return r;
}
#[no_mangle] pub unsafe extern "C" fn lil_free(mut lil: lil_t) {
    if lil.is_null() { return; }
    free((*lil).env as *mut core::ffi::c_void);
    free(lil as *mut core::ffi::c_void);
}
#[no_mangle] pub unsafe extern "C" fn run(code: *const u8, len: usize) -> i32 {
    let mut lil = lil_new();
    let r = lil_parse(lil, code, len);
    lil_free(lil);
    return r;
}
"#;

/// W63 (R580-1): a context whose writer invokes a callback installed in it,
/// with the context as the callback's argument.
const W63_CALLBACK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case, unused_mut)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; fn free(_: *mut core::ffi::c_void); }
#[repr(C)] pub struct ctx_t { pub n: i32, pub cb: Option<unsafe extern "C" fn(*mut ctx_t) -> i32> }
unsafe extern "C" fn set_var(mut c: *mut ctx_t, v: i32) {
    (*c).n = v;
    if (*c).cb.is_some() { (*c).cb.expect("non-null function pointer")(c); }
}
unsafe extern "C" fn get_var(mut c: *mut ctx_t) -> i32 { return (*c).n; }
#[no_mangle] pub unsafe extern "C" fn run(v: i32) -> i32 {
    let mut c = malloc(core::mem::size_of::<ctx_t>() as u64) as *mut ctx_t;
    (*c).n = 0; (*c).cb = None;
    set_var(c, v);
    let r = get_var(c);
    free(c as *mut core::ffi::c_void);
    return r;
}
"#;

/// W67 (R607-1): small shapes for the raw-cause ledger's classes -- a pointer
/// joined at a phi with null or with a borrowed pointer, and locals no rule
/// reaches.
const W67_SHAPES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case, unused_mut, unused_assignments)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; fn free(_: *mut core::ffi::c_void); }
#[no_mangle] pub unsafe extern "C" fn phi_null(c: i32) -> i32 {
    let mut p: *mut i32 = 0 as *mut i32;
    if c != 0 { p = malloc(4) as *mut i32; *p = c; }
    let r = if p.is_null() { 0 } else { *p };
    free(p as *mut core::ffi::c_void);
    r
}
#[no_mangle] pub unsafe extern "C" fn phi_join(c: i32, q: *mut i32) -> i32 {
    let mut p: *mut i32 = if c != 0 { malloc(4) as *mut i32 } else { q };
    *p = 1;
    *p
}
#[no_mangle] pub unsafe extern "C" fn pick(a: *mut i32, b: *mut i32, c: i32) -> i32 {
    let mut p: *mut i32 = if c != 0 { a } else { b };
    *p
}
#[repr(C)] pub struct S { pub p: *mut i32 }
#[no_mangle] pub unsafe extern "C" fn two(s: *mut S, a: *mut i32, b: *mut i32, c: i32) -> i32 {
    if c != 0 { (*s).p = a; } else { (*s).p = b; }
    (*s).p = (*s).p.offset(1);
    *a + *b
}
#[repr(C)] pub struct N { pub l: *mut N, pub r: *mut N }
pub unsafe fn del(root: *mut N) -> *mut N {
    if root.is_null() { return root; }
    if (*root).l.is_null() {
        let t = (*root).r;
        free(root as *mut core::ffi::c_void);
        return t;
    }
    return root;
}
#[no_mangle] pub unsafe extern "C" fn keep(a: *mut i32) -> *mut i32 {
    let mut p: *mut i32 = a;
    let mut t: *mut i32 = p;
    t
}
"#;

/// W68 (R609-3): W64d's two walls, reduced. `tree_insert` reads the container
/// in the argument list of the call that receives its reborrow (quadtree's
/// `insert_(tree, (*tree).root, …)`); `reset_` writes through `tree` while the
/// reborrow of `node` it passes on is live, the two formals A5 overlap partners
/// of incompatible types (quadtree's `reset_node_`); `same_` is that shape with
/// both formals of one type, the control.
const W68_SHAPES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case, unused_mut, unused_assignments)]
#[repr(C)] pub struct node_t { pub v: i32, pub next: *mut node_t }
#[repr(C)] pub struct tree_t { pub root: *mut node_t, pub n: u32 }
unsafe extern "C" fn insert_(tree: *mut tree_t, root: *mut node_t, v: i32) -> i32 {
    (*root).v = v;
    (*tree).n = (*tree).n.wrapping_add(1);
    1
}
#[no_mangle] pub unsafe extern "C" fn tree_insert(tree: *mut tree_t, v: i32) -> i32 {
    if insert_(tree, (*tree).root, v) == 0 { return 0; }
    (*tree).n = (*tree).n.wrapping_add(1);
    1
}
unsafe extern "C" fn node_reset(node: *mut node_t) { (*node).v = 0; }
unsafe extern "C" fn reset_(tree: *mut tree_t, node: *mut node_t) {
    let mut n = node;
    (*tree).n = 0;
    node_reset(n);
}
#[no_mangle] pub unsafe extern "C" fn tree_reset(tree: *mut tree_t) { reset_(tree, (*tree).root); }
unsafe extern "C" fn same_(a: *mut node_t, b: *mut node_t) {
    let mut n = b;
    (*a).v = 1;
    node_reset(n);
}
#[no_mangle] pub unsafe extern "C" fn node_same(a: *mut node_t) { same_(a, (*a).next); }
"#;

/// The W63 child: the shape's model, the lend plan, and every licensing
/// snapshot of an export-capturing solve re-validated.
#[test]
#[ignore = "runs under L01¹⁰'s arms in a child of the W63 witnesses"]
fn e5c_inner_w63() {
    use rustc_hir::{ItemKind, OwnerNode};
    let owned;
    let shape = match std::env::var("CRAT_E5C_W63_SHAPE").as_deref() {
        Ok("ctx") => W63_CTX,
        Ok("callback") => W63_CALLBACK,
        Ok("w66-controls") => W66_CONTROLS,
        Ok("w67-shapes") => W67_SHAPES,
        Ok("w68-shapes") => W68_SHAPES,
        Ok("w71-shapes") => W71_SHAPES,
        Ok("ctx-jail") => W71_CTX_JAIL,
        Ok("w74-shapes") => W74_SHAPES,
        Ok("w75-shapes") => W75_SHAPES,
        Ok("w79-shapes") => W79_SHAPES,
        Ok("w83-swap") => W83_SWAP,
        Ok("w84-null") => W84_LIST,
        Ok("w84-zero") => {
            owned = W84_LIST.replace(W84_NULL_ITEM, "");
            owned.as_str()
        }
        Ok("w85-call") => W85_G,
        Ok("w85-cast") => {
            owned = W85_G.replace("::core::ptr::null_mut::<Node>()", "0 as *mut Node");
            owned.as_str()
        }
        Ok("w84-static") => {
            owned = format!("{W84_LIST}{W84_STATIC}");
            owned.as_str()
        }
        Ok(file) if file.starts_with("file:") => {
            owned = std::fs::read_to_string(&file[5..]).expect("the W64 program");
            owned.as_str()
        }
        other => panic!("CRAT_E5C_W63_SHAPE: {other:?}"),
    };
    shape_model(shape);
    // W64d reads the model alone.
    if std::env::var_os("CRAT_E5C_W63_MODEL_ONLY").is_some() {
        return;
    }
    ::utils::compilation::run_compiler_on_str(shape, |tcx| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let plan = super::licensing::lend::collect(&program);
        for (function, formal) in &plan.lendable {
            eprintln!("E5C_W63 lendable {function}::_{formal}");
        }
        for site in &plan.waivers {
            eprintln!(
                "E5C_W63 waiver {} id={}",
                site.receipt(),
                super::licensing::lend::WAIVER_ID
            );
        }
        let slots = super::crate_slots::CrateSlots::build(&program);
        let origins = super::origins::compute_origins(&program);
        let mutability = super::mutability_facts::MutFacts::from_program(&program);
        let (verified, captured) = super::export::with_bo_export(|| {
            super::construction::solve_bo_a5_config_reporting(
                &program,
                &slots,
                &origins,
                &mutability,
                super::a5_overlap::A5Mode::PreciseReplay,
                Some(super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
            )
            .expect("W63 needs an accepted model")
        });
        for snapshot in captured.ownership_licensing.iter().flatten() {
            match snapshot.validate() {
                Ok(()) => eprintln!(
                    "E5C_W63 validate ok lend_plan={}",
                    snapshot.lend_plan.is_some()
                ),
                Err(e) => eprintln!("E5C_W63 validate err:{e}"),
            }
        }
        // W66 (R603-2): the final retirement review's discharges and conflicts.
        if let Some(review) = &captured.source_retirement {
            for row in &review.discharged {
                eprintln!("E5C_W63 discharge {}", row.receipt());
            }
            for row in &review.conflicts {
                eprintln!(
                    "E5C_W63 retire-conflict {} {}:bb{}[{}] {:?}",
                    row.target_key,
                    row.source.function,
                    row.source.block,
                    row.source.statement,
                    row.overlap
                );
            }
        }
        // W76 (R677-4): the final review's discharged rows in the in-memory packet
        // and in the prepared (streamed) entry.
        if std::env::var_os("CRAT_E5C_W76").is_some() {
            let mode = super::a5_overlap::A5Mode::PreciseReplay;
            let attestation =
                Some(super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph);
            let discharged = |v: &serde_json::Value| {
                v["families"]["retirement-final"]["records"][0]["fields"]["discharged"].clone()
            };
            // W79 (R690-6): a refused export is a line, so the fault's child exits cleanly.
            let packet = match super::portable_export::collect(&program, &slots, &captured) {
                Ok(packet) => packet,
                Err(error) => {
                    eprintln!("E5C_W63 export-refused {error}");
                    return;
                }
            };
            let portable: serde_json::Value =
                serde_json::from_str(&packet.canonical_json().unwrap()).unwrap();
            let inputs = super::model_cache::semantic_inputs(&program, mode, attestation).unwrap();
            let key = super::cache_contract::semantic_key(&inputs).unwrap();
            super::model_cache::prepare(
                &program,
                &slots,
                &origins,
                &verified,
                &captured,
                mode,
                attestation,
            );
            let entry = super::model_cache::prepared_entry(&key).unwrap_or_else(|| {
                panic!(
                    "the prepared entry: {:?}",
                    super::model_cache::prepare_error()
                )
            });
            let (p, e) = (discharged(&portable), discharged(&entry.exports));
            let count = |v: &serde_json::Value| v.as_array().map_or(0, Vec::len);
            eprintln!(
                "E5C_W63 discharged portable={} entry={} equal={}",
                count(&p),
                count(&e),
                p == e
            );
        }
        // W68 (R609-3): the A5 receipt's type-route keys.
        for line in verified.receipt.lines() {
            if line.starts_with("a5_type_disjoint") {
                eprintln!("E5C_W63 a5-receipt {line}");
            }
        }
        // W72 (R659-1): the arm-(a) receipts from the model, the portable
        // export and the prepared cache entry.
        if std::env::var_os("CRAT_E5C_W72").is_some() {
            let mode = super::a5_overlap::A5Mode::PreciseReplay;
            let attestation =
                Some(super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph);
            let model = super::portable_export::arg_order_rows(&program, &slots, &captured)
                .expect("rows convert");
            let packet = super::portable_export::collect(&program, &slots, &captured).unwrap();
            let decoded: super::portable_export::PortableExport =
                serde_json::from_str(&packet.canonical_json().unwrap()).unwrap();
            let portable = decoded.arg_order_applied();
            let inputs = super::model_cache::semantic_inputs(&program, mode, attestation).unwrap();
            let key = super::cache_contract::semantic_key(&inputs).unwrap();
            super::model_cache::prepare(
                &program,
                &slots,
                &origins,
                &verified,
                &captured,
                mode,
                attestation,
            );
            let entry = super::model_cache::prepared_arg_order_applied(&key);
            let describe =
                |rows: &Result<Vec<super::portable_export::ArgOrderRow>, String>| match rows {
                    Ok(rows) => format!("ok:{}", rows.len()),
                    Err(e) => format!("err:{e}"),
                };
            eprintln!(
                "E5C_W63 arg-order model={} portable={} entry={} equal={}",
                model
                    .as_ref()
                    .map_or("none".into(), |m| m.len().to_string()),
                describe(&portable),
                describe(&entry),
                model
                    .as_ref()
                    .is_some_and(|m| portable.as_ref().is_ok_and(|p| p == m)
                        && entry.as_ref().is_ok_and(|e| e == m))
            );
            // R666-1: the loader's keys, spans re-read from this session's MIR.
            match super::model_cache::prepared_arg_order_hoists(tcx, &key) {
                Ok(hoists) => {
                    for ((lo, hi), caller, lent) in hoists {
                        let span = rustc_span::Span::with_root_ctxt(
                            rustc_span::BytePos(lo),
                            rustc_span::BytePos(hi),
                        );
                        let text = tcx
                            .sess
                            .source_map()
                            .span_to_snippet(span)
                            .unwrap_or_default()
                            .split_whitespace()
                            .collect::<Vec<_>>()
                            .join(" ");
                        eprintln!(
                            "E5C_W63 arg-order-hoist {} lent=_{} text={text}",
                            tcx.def_path_str(caller.to_def_id()),
                            lent.as_u32()
                        );
                    }
                }
                Err(e) => eprintln!("E5C_W63 arg-order-hoist err:{e}"),
            }
            for row in model.iter().flatten() {
                eprintln!(
                    "E5C_W63 arg-order-row {} bb{}[{}] lent=_{} owner=_{} span={}..{}",
                    row.function,
                    row.call.block,
                    row.call.statement,
                    row.lent,
                    row.owner,
                    row.span.lo,
                    row.span.hi
                );
            }
        }
        // W69 (R617-1): the receipt's repair stamp and the residual certificate.
        for line in verified.receipt.lines() {
            if line.starts_with("repair=") || line.starts_with("guarded_") {
                eprintln!("E5C_W63 repair-receipt {line}");
            }
        }
        eprintln!(
            "E5C_W63 residuals {}",
            captured
                .residual_conflicts
                .as_ref()
                .map_or_else(|| "none".to_owned(), |rows| rows.len().to_string())
        );
        // W67 (R607-1): the raw-cause ledger of the accepted model.
        if super::raw_cause::enabled() {
            for row in super::raw_cause::last().unwrap_or_default() {
                eprintln!("E5C_W63 ledger {}", row.tsv());
            }
        }
    })
    .unwrap();
}

fn w63_lines(shape: &str, extra: &[(&str, &str)]) -> Vec<String> {
    w63_child(shape, extra)
        .lines()
        .filter_map(|l| {
            l.find("E5C_W63 ")
                .map(|i| l[i + 8..].to_owned())
                .or_else(|| l.find("E5C_MODEL ").map(|i| l[i + 10..].to_owned()))
        })
        .collect()
}

fn w63_child(shape: &str, extra: &[(&str, &str)]) -> String {
    let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
    env.extend_from_slice(&[
        ("CRAT_ERA5C_MUT_MODEL", "on"),
        ("CRAT_ERA5C_ORIGIN_SET", "on"),
        ("CRAT_ERA5C_DEREF_READER", "on"),
        ("CRAT_ERA5C_MOVED_INPUT", "on"),
        ("CRAT_ERA5C_FIELD_OWN_REPAIR", "on"),
        ("CRAT_ERA5C_MOVE_STORE", "on"),
        // L01¹⁰'s configuration (R604-1): the typed-release discharge is on.
        ("CRAT_ERA5C_TYPED_RELEASE", "on"),
        // L01¹⁰'s configuration (R609-3): the argument-order premise and the
        // A5 type route are on.
        ("CRAT_ERA5C_ARG_ORDER", "on"),
        ("CRAT_ERA5C_OVERLAP_TYPE_ROUTE", "on"),
        ("CRAT_E5C_W63_SHAPE", shape),
    ]);
    env.extend_from_slice(extra);
    child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_w63",
        &env,
    )
}

fn w63_kind(lines: &[String], key: &str) -> String {
    lines
        .iter()
        .find_map(|l| l.strip_prefix(&format!("{key} ")).map(str::to_owned))
        .unwrap_or_else(|| panic!("no {key}: {lines:?}"))
}

/// W63a: with the lend, the context's pass-through formals are not Owning --
/// every call lends them; without it they take the owner (062's wall, RED).
#[test]
fn e5c_w63_a_a_lendable_formal_is_a_zero_view_at_every_call() {
    let on = w63_lines("ctx", &[("CRAT_ERA5C_LEND", "on")]);
    let off = w63_lines("ctx", &[("CRAT_ERA5C_LEND", "off")]);
    // R590-5 L-G (W64b): every lent context formal is Ref, not merely "not
    // Owning" -- 070b's Raw passed the weaker claim.
    for f in [
        "ateol",
        "skip_spaces",
        "lil_push_env",
        "lil_pop_env",
        "lil_parse",
    ] {
        let key = format!("{f}::_1@d0");
        assert!(
            on.iter().any(|l| l == &format!("lendable {f}::_1")),
            "{on:?}"
        );
        assert_eq!(w63_kind(&on, &key), "ref", "{key} lends: {on:?}");
        assert_eq!(
            w63_kind(&off, &key),
            "owning",
            "{key} without the lend: {off:?}"
        );
    }
}

/// W63b: a consuming callee still takes the owner -- `lil_free` frees its
/// formal, is no lend, and stays Owning with the arm; the constructor's owner
/// reaches it.
#[test]
fn e5c_w63_b_a_consuming_formal_keeps_the_owner() {
    let on = w63_lines("ctx", &[("CRAT_ERA5C_LEND", "on")]);
    assert!(!on.iter().any(|l| l == "lendable lil_free::_1"), "{on:?}");
    assert_eq!(w63_kind(&on, "lil_free::_1@d0"), "owning", "{on:?}");
    assert_eq!(w63_kind(&on, "lil_new::_0@d0"), "owning", "{on:?}");
}

/// W63c (R580-1): a member handed to an indirect callee is no consumer; the
/// site is receipted under R481's tier-2 waiver. Under `no-waiver` the
/// indirect call consumes again (RED).
#[test]
fn e5c_w63_c_an_indirect_call_lends_under_the_tier_2_waiver() {
    let on = w63_lines("callback", &[("CRAT_ERA5C_LEND", "on")]);
    assert!(on.iter().any(|l| l == "lendable set_var::_1"), "{on:?}");
    assert_eq!(
        on.iter().filter(|l| l.starts_with("waiver ")).count(),
        1,
        "one site: {on:?}"
    );
    assert!(
        on.iter().any(|l| l
            .starts_with("waiver lend-waiver(tier-2, kind=indirect-call, site=set_var:bb")
            && l.ends_with("id=retention-waiver:tier-2@2026-09-21")),
        "{on:?}"
    );
    let fault = w63_lines(
        "callback",
        &[
            ("CRAT_ERA5C_LEND", "on"),
            ("CRAT_E5C_W63_FAULT", "no-waiver"),
        ],
    );
    assert!(
        !fault.iter().any(|l| l == "lendable set_var::_1"),
        "RED: {fault:?}"
    );
    assert!(!fault.iter().any(|l| l.starts_with("waiver ")), "{fault:?}");
}

/// W63e: the recorded plan travels in the licensing snapshot and a restored
/// snapshot validates; under `lend-all` (every pointer argument borrowed, the
/// plan honest) the validator refuses the uncertified borrowed calls (RED).
#[test]
fn e5c_w63_e_the_validator_refuses_an_uncertified_borrowed_call() {
    let on = w63_lines("ctx", &[("CRAT_ERA5C_LEND", "on")]);
    assert!(
        on.iter().any(|l| l == "validate ok lend_plan=true"),
        "{on:?}"
    );
    assert!(!on.iter().any(|l| l.starts_with("validate err")), "{on:?}");
    let fault = w63_lines(
        "ctx",
        &[
            ("CRAT_ERA5C_LEND", "on"),
            ("CRAT_E5C_W63_FAULT", "lend-all"),
        ],
    );
    assert!(
        fault
            .iter()
            .any(|l| l == "validate err:lent call has no lend certificate"),
        "RED: {fault:?}"
    );
}

/// era-5c 070: the production lend plan (`licensing::lend::collect`) of one
/// program's `lib.rs` (`CRAT_E5C_LEND_INPUT`): its lendable formals and its
/// R580-1 waiver receipts. A MIR walk, no solver.
#[test]
#[ignore = "era-5c 070: the lend plan of a named program, no solver"]
fn e5c_lend_plan_of() {
    use rustc_hir::{ItemKind, OwnerNode};
    let path = std::env::var("CRAT_E5C_LEND_INPUT").expect("CRAT_E5C_LEND_INPUT");
    let source = std::fs::read_to_string(&path).expect("source");
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let mut functions = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            if let ItemKind::Fn { .. } = item.kind {
                functions.push(item.owner_id.def_id);
            }
        }
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs: Vec::new(),
        };
        let plan = super::licensing::lend::collect(&program);
        for (function, formal) in &plan.lendable {
            eprintln!("E5C_LEND_PLAN lendable {function}::_{formal}@d0");
        }
        for site in &plan.waivers {
            eprintln!("E5C_LEND_PLAN waiver {}", site.receipt());
        }
        eprintln!(
            "E5C_LEND_PLAN total lendable={} waivers={}",
            plan.lendable.len(),
            plan.waivers.len()
        );
    })
    .unwrap();
}

const W64_HT: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/rs-crown-derived/ht/lib.rs"
);

/// W64a (R590-5, the record §5): ht's `ht_expand` frees and replaces
/// `(*table).entries`; `ht_set` calls it. With the lend both `table` formals
/// are **Ref** and the `entries` field stays **Owning** -- the interior
/// component carries the field's ownership through the call. RED: the
/// full-window lend of 070 (`full-window`) sends the tables to Raw.
#[test]
fn e5c_w64_a_a_lent_writer_moves_the_field_not_the_container() {
    if !std::path::Path::new(W64_HT).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let shape = format!("file:{W64_HT}");
    let on = w63_lines(&shape, &[("CRAT_ERA5C_LEND", "on")]);
    for key in ["src::ht::ht_expand::_1@d0", "src::ht::ht_set::_1@d0"] {
        assert_eq!(w63_kind(&on, key), "ref", "{key}: {on:?}");
    }
    assert_eq!(w63_kind(&on, "src::ht::ht::field0@d0"), "owning", "{on:?}");
    let fault = w63_lines(
        &shape,
        &[
            ("CRAT_ERA5C_LEND", "on"),
            ("CRAT_E5C_W64_FAULT", "full-window"),
            // R609-3: the discharge would remove the conflict the fault acts through.
            ("CRAT_E5C_W66_FAULT", "no-discharge"),
        ],
    );
    assert_eq!(
        w63_kind(&fault, "src::ht::ht_expand::_1@d0"),
        "raw",
        "RED: {fault:?}"
    );
}

/// W64d (R590-5 L-C, a LANDING GATE; restated R631-6): the no-loss control
/// on the five. With the lend no slot falls to Raw and no Ref becomes Owning;
/// the gains (raw -> ref, owning -> ref, raw -> owning) are allowed and listed.
#[test]
fn e5c_w64_d_no_slot_of_the_five_falls() {
    let root = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/rs-crown-derived"
    );
    for program in ["bst", "avl", "ht", "buffer", "quadtree"] {
        let path = format!("{root}/{program}/lib.rs");
        if !std::path::Path::new(&path).is_file() {
            eprintln!("corpus absent; skipping {program}");
            continue;
        }
        let shape = format!("file:{path}");
        let model = |lend: &str| -> std::collections::BTreeMap<String, String> {
            w63_lines(
                &shape,
                &[("CRAT_ERA5C_LEND", lend), ("CRAT_E5C_W63_MODEL_ONLY", "1")],
            )
            .into_iter()
            .filter_map(|l| {
                let (k, v) = l.rsplit_once(' ')?;
                k.contains("@d").then(|| (k.to_owned(), v.to_owned()))
            })
            .collect()
        };
        let (off, on) = (model("off"), model("on"));
        assert_eq!(off.len(), on.len(), "{program}: the slot universe");
        let moved: Vec<_> = off
            .iter()
            .filter(|(k, v)| on.get(*k) != Some(*v))
            .map(|(k, v)| format!("{k} {v}->{}", on[k]))
            .collect();
        eprintln!("E5C_W64D {program} moved={} {moved:?}", moved.len());
        let lost: Vec<_> = moved
            .iter()
            .filter(|m| m.ends_with("->raw") || m.ends_with("ref->owning"))
            .collect();
        assert!(lost.is_empty(), "{program}: a slot fell: {lost:?}");
    }
}

/// W64f (R659-1, R668-4: W64d restated for L01¹¹, losses only): on the five and
/// `ctx`, L01¹⁰'s configuration (the lend on) against every L01¹¹ switch on --
/// the zero law, (γ), (α⁺), (β′), (α)'s route condition and the allocator
/// contract. No slot falls to Raw and no Ref becomes Owning; every move is
/// printed (`E5C_W64F`).
#[test]
fn e5c_w64_f_no_slot_of_the_six_falls_under_l01p11() {
    const L01P11: [&str; 6] = [
        "CRAT_ERA5C_REF_PEEL_ZERO",
        "CRAT_ERA5C_RETIRE_FRESH",
        "CRAT_ERA5C_RETIRE_ROUTE_USE",
        "CRAT_ERA5C_TYPED_SOLE",
        "CRAT_ERA5C_ALPHA_RETURNS",
        "CRAT_ERA5C_ALLOCATOR_CONTRACT",
    ];
    let root = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/rs-crown-derived"
    );
    let mut shapes = vec![("ctx".to_owned(), "ctx".to_owned())];
    for program in ["bst", "avl", "ht", "buffer", "quadtree"] {
        let path = format!("{root}/{program}/lib.rs");
        if std::path::Path::new(&path).is_file() {
            shapes.push((program.to_owned(), format!("file:{path}")));
        } else {
            eprintln!("corpus absent; skipping {program}");
        }
    }
    for (program, shape) in &shapes {
        let model = |value: &str| -> std::collections::BTreeMap<String, String> {
            let mut env = vec![("CRAT_ERA5C_LEND", "on"), ("CRAT_E5C_W63_MODEL_ONLY", "1")];
            env.extend(L01P11.iter().map(|switch| (*switch, value)));
            w63_lines(shape, &env)
                .into_iter()
                .filter_map(|l| {
                    let (k, v) = l.rsplit_once(' ')?;
                    k.contains("@d").then(|| (k.to_owned(), v.to_owned()))
                })
                .collect()
        };
        let (off, on) = (model("off"), model("on"));
        assert_eq!(off.len(), on.len(), "{program}: the slot universe");
        let moved: Vec<_> = off
            .iter()
            .filter(|(k, v)| on.get(*k) != Some(*v))
            .map(|(k, v)| format!("{k} {v}->{}", on[k]))
            .collect();
        eprintln!("E5C_W64F {program} moved={} {moved:?}", moved.len());
        let lost: Vec<_> = moved
            .iter()
            .filter(|m| m.ends_with("->raw") || m.ends_with("ref->owning"))
            .collect();
        assert!(lost.is_empty(), "{program}: a slot fell: {lost:?}");
    }
}

/// W64e (R590-5 L-B): the validator refuses a `Lent` row with an interior
/// zero, one missing an interior equality, and one whose certificate is
/// absent from the snapshot (three faults, each RED).
#[test]
fn e5c_w64_e_the_validator_refuses_a_malformed_lent_row() {
    let on = w63_lines("ctx", &[("CRAT_ERA5C_LEND", "on")]);
    assert!(
        on.iter().any(|l| l == "validate ok lend_plan=true"),
        "{on:?}"
    );
    for (fault, message) in [
        (
            "interior-zero",
            "validate err:lent call zeroes an interior component",
        ),
        (
            "no-interior-equal",
            "validate err:boundary matched pair has no corresponding emitted equation",
        ),
        (
            "drop-plan",
            "validate err:lent call has no lend certificate",
        ),
    ] {
        let lines = w63_lines(
            "ctx",
            &[("CRAT_ERA5C_LEND", "on"), ("CRAT_E5C_W64_FAULT", fault)],
        );
        assert!(lines.iter().any(|l| l == message), "{fault}: {lines:?}");
    }
}

// ---- era-5c 077 / R603-2: the retirement discharges. (α) the post-free use,
// unconditional; (β) the effective type behind CRAT_ERA5C_TYPED_RELEASE, which
// rests on the premise TypedReleaseDiscipline (R603-1, the user's).

const W66_QUADTREE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/rs-crown-derived/quadtree/lib.rs"
);

fn w66_lines(shape: &str, typed: &str, fault: Option<&str>) -> Vec<String> {
    let mut extra = vec![
        ("CRAT_ERA5C_LEND", "on"),
        ("CRAT_ERA5C_TYPED_RELEASE", typed),
    ];
    if let Some(fault) = fault {
        extra.push(("CRAT_E5C_W66_FAULT", fault));
    }
    w63_lines(shape, &extra)
}

/// W66a: ht's lent tables are Ref and `entries` Owning under the discharge;
/// every discharge is receipted. RED: `no-discharge` gives 072's Raw back.
#[test]
fn e5c_w66_a_ht_tables_return_to_ref_under_the_discharge() {
    if !std::path::Path::new(W64_HT).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let shape = format!("file:{W64_HT}");
    let on = w66_lines(&shape, "on", None);
    for key in ["src::ht::ht_expand::_1@d0", "src::ht::ht_set::_1@d0"] {
        assert_eq!(w63_kind(&on, key), "ref", "{key}: {on:?}");
    }
    assert_eq!(w63_kind(&on, "src::ht::ht::field0@d0"), "owning", "{on:?}");
    assert!(
        on.iter()
            .any(|l| l.starts_with("discharge retirement-disjoint:")
                && l.contains("target=src::ht::ht_expand::_1@d0")),
        "{on:?}"
    );
    let red = w66_lines(&shape, "on", Some("no-discharge"));
    assert_eq!(
        w63_kind(&red, "src::ht::ht_expand::_1@d0"),
        "raw",
        "RED: {red:?}"
    );
    assert!(!red.iter().any(|l| l.starts_with("discharge ")), "{red:?}");
}

/// W66b: lil's context shape; the two formals 072 lost are Ref again.
#[test]
fn e5c_w66_b_the_context_formals_return_to_ref_under_the_discharge() {
    let on = w66_lines("ctx", "on", None);
    for key in ["lil_parse::_1@d0", "lil_pop_env::_1@d0"] {
        assert_eq!(w63_kind(&on, key), "ref", "{key}: {on:?}");
    }
    let red = w66_lines("ctx", "on", Some("no-discharge"));
    assert_eq!(w63_kind(&red, "lil_pop_env::_1@d0"), "raw", "RED: {red:?}");
}

/// W66c: quadtree's four `::tree` formals are Ref again; each rests on the
/// premise (an effective-type receipt).
#[test]
fn e5c_w66_c_quadtrees_four_return_to_ref_under_the_discharge() {
    if !std::path::Path::new(W66_QUADTREE).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let shape = format!("file:{W66_QUADTREE}");
    let on = w66_lines(&shape, "on", None);
    for function in ["insert_", "quadtree_insert", "reset_node_", "split_node_"] {
        let key = format!("src::src::quadtree::{function}::_1@d0");
        assert_eq!(w63_kind(&on, &key), "ref", "{key}: {on:?}");
    }
    assert!(
        on.iter()
            .any(|l| l.contains("retirement-disjoint:effective-type(")
                && l.contains("target=src::src::quadtree::reset_node_::_1@d0")
                && l.ends_with("premise=typed-release@R604-1)")),
        "{on:?}"
    );
    let red = w66_lines(&shape, "on", Some("no-discharge"));
    assert_eq!(
        w63_kind(&red, "src::src::quadtree::reset_node_::_1@d0"),
        "raw",
        "RED: {red:?}"
    );
}

/// W66's controls: a `void` free, a referent embedding the freed type by
/// value and a union give no discharge; unrelated types discharge under the
/// premise only; the carve discharges too, which is exactly what the premise
/// excludes (its receipt names the premise).
const W66_CONTROLS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, unused_mut, non_camel_case_types, non_snake_case)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; fn free(_: *mut core::ffi::c_void); }
#[repr(C)] #[derive(Clone, Copy)] pub struct P { pub x: i32, pub y: i32 }
#[repr(C)] pub struct T { pub n: i32, pub m: i32 }
#[repr(C)] pub struct E { pub inner: P, pub n: i32 }
#[repr(C)] pub union U { pub p: P, pub n: i64 }
unsafe fn release(q: *mut core::ffi::c_void) { free(q); }
pub unsafe fn void_free(t: *mut T, q: *mut core::ffi::c_void) -> i32 { let r = (*t).n; release(q); return r; }
pub unsafe fn embedded(e: *mut E, p: *mut P) -> i32 { let r = (*e).n; free(p as *mut core::ffi::c_void); return r; }
pub unsafe fn unioned(u: *mut U, p: *mut P) -> i64 { let r = (*u).n; free(p as *mut core::ffi::c_void); return r; }
pub unsafe fn typed(t: *mut T, p: *mut P) -> i32 { let r = (*t).n; free(p as *mut core::ffi::c_void); return r; }
pub unsafe fn carved_use(t: *mut T, p: *mut P) -> i32 { let r = (*t).n; free(p as *mut core::ffi::c_void); return r; }
pub unsafe fn carve() -> i32 {
    let p = malloc(64) as *mut P;
    let t = (p as *mut u8).offset(32) as *mut T;
    (*p).x = 1; (*t).n = 2;
    return carved_use(t, p);
}
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let t = malloc(8) as *mut T; let e = malloc(12) as *mut E; let u = malloc(8) as *mut U;
    (*t).n = 1; (*e).n = 2; (*u).n = 3;
    let r = void_free(t, malloc(8)) + embedded(e, malloc(8) as *mut P)
        + unioned(u, malloc(8) as *mut P) as i32 + typed(t, malloc(8) as *mut P) + carve();
    free(t as *mut core::ffi::c_void); free(e as *mut core::ffi::c_void); free(u as *mut core::ffi::c_void);
    return r;
}
"#;

#[test]
fn e5c_w66_controls_void_embedded_union_and_the_carve() {
    let discharges = |lines: &[String], function: &str| -> Vec<String> {
        lines
            .iter()
            .filter(|l| {
                l.starts_with("discharge ") && l.contains(&format!("target={function}::_1@d0"))
            })
            .cloned()
            .collect()
    };
    let on = w66_lines("w66-controls", "on", None);
    for function in ["void_free", "embedded", "unioned"] {
        assert!(discharges(&on, function).is_empty(), "{function}: {on:?}");
    }
    for function in ["typed", "carved_use"] {
        let rows = discharges(&on, function);
        assert!(
            !rows.is_empty()
                && rows
                    .iter()
                    .all(|l| l.ends_with("premise=typed-release@R604-1)")),
            "{function}: {on:?}"
        );
    }
    let off = w66_lines("w66-controls", "off", None);
    assert!(
        !off.iter()
            .any(|l| l.contains("retirement-disjoint:effective-type(")),
        "no effective-type discharge without the premise: {off:?}"
    );
}

/// 077's census for a program too large to solve here (brotli): every heap
/// release in the MIR, its freed type recovered in its own frame and, where
/// that ends at a parameter, from each direct caller's argument. No solver.
#[test]
#[ignore = "era-5c 077: the freed types of a named program, MIR only"]
fn e5c_free_types_of() {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::mir::TerminatorKind;
    let path = std::env::var("CRAT_E5C_RD_INPUT").expect("CRAT_E5C_RD_INPUT");
    let source = std::fs::read_to_string(&path).expect("source");
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let mut functions = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            if let ItemKind::Fn { .. } = item.kind {
                functions.push(item.owner_id.def_id);
            }
        }
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions: functions.clone(),
            structs: Vec::new(),
        };
        let events = super::source_events::collect(&program);
        let names: std::collections::BTreeMap<String, _> = functions
            .iter()
            .map(|&f| (tcx.def_path_str(f), f))
            .collect();
        let mut table = super::retirement::discharge::Discharges::default();
        let mut tally = std::collections::BTreeMap::<String, usize>::new();
        for (key, row) in &events.retirements {
            if !matches!(
                key.role,
                super::source_events::SourceRole::Free
                    | super::source_events::SourceRole::ReallocOld
            ) {
                continue;
            }
            let super::source_events::SourceObject::HeapThrough(place) = &row.object else {
                continue;
            };
            let Some(&function) = names.get(&key.function) else { continue };
            let local = table.recover(tcx, function, function, place.clone(), &[]);
            let mut rows = vec![("own-frame".to_owned(), local)];
            if rows[0].1.is_none() {
                for &caller in &functions {
                    let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
                    for (bb, data) in body.basic_blocks.iter_enumerated() {
                        let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                            continue;
                        };
                        let Some((callee, _)) = func.const_fn_def() else { continue };
                        if callee != function.to_def_id() {
                            continue;
                        }
                        let step = super::retirement::RouteStep {
                            caller,
                            callee: function,
                            location: rustc_middle::mir::Location {
                                block: bb,
                                statement_index: data.statements.len(),
                            },
                        };
                        let found = table.recover(tcx, caller, function, place.clone(), &[step]);
                        rows.push((format!("caller {}", tcx.def_path_str(caller)), found));
                    }
                }
            }
            for (via, found) in rows {
                let name = found
                    .as_ref()
                    .map_or("none".to_owned(), |t| table.name_of(t));
                eprintln!(
                    "E5C_FREE {}:bb{}[{}] {:?} via={via} P={name}",
                    key.function, key.block, key.statement, key.role
                );
                *tally
                    .entry(if found.is_some() {
                        "typed".into()
                    } else {
                        "none".into()
                    })
                    .or_default() += 1;
            }
        }
        eprintln!("E5C_FREE total {tally:?}");
    })
    .unwrap();
}

/// W67 (R607-1 leg A): the raw-cause ledger's rows, from the W63 child with L01¹⁰'s
/// arms and the lend on. `CRAT_E5C_W67_FAULT=no-ledger` (test builds) silences the
/// ledger: every W67 witness is RED under it.
fn w67_rows(shape: &str, extra: &[(&str, &str)]) -> Vec<Vec<String>> {
    let mut env = vec![
        ("CRAT_ERA5C_LEND", "on"),
        ("CRAT_ERA5C_RAW_CAUSE_LEDGER", "on"),
    ];
    env.extend_from_slice(extra);
    w63_lines(shape, &env)
        .iter()
        .filter_map(|l| l.strip_prefix("ledger "))
        .map(|row| row.split('\t').map(str::to_owned).collect())
        .collect()
}

fn w67_row<'a>(rows: &'a [Vec<String>], key: &str) -> &'a Vec<String> {
    rows.iter()
        .find(|row| row[0] == key)
        .unwrap_or_else(|| panic!("no ledger row {key}: {rows:?}"))
}

/// W67a: ht's `ht_expand::_1` without the discharge is Raw by its own
/// retirement conflict; with the discharge it is Ref and has no row.
#[test]
fn e5c_w67_a_the_ledger_names_a_retirement_conflict() {
    if !std::path::Path::new(W64_HT).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let shape = format!("file:{W64_HT}");
    let red = w67_rows(&shape, &[("CRAT_E5C_W66_FAULT", "no-discharge")]);
    let row = w67_row(&red, "src::ht::ht_expand::_1@d0");
    assert_eq!(
        (row[2].as_str(), row[3].as_str(), row[6].as_str()),
        ("retirement-conflict", "src::ht::ht_expand::_1@d0", "direct"),
        "{row:?}"
    );
    let on = w67_rows(&shape, &[]);
    assert!(
        !on.iter().any(|row| row[0] == "src::ht::ht_expand::_1@d0"),
        "{on:?}"
    );
    let off = w67_rows(
        &shape,
        &[
            ("CRAT_E5C_W66_FAULT", "no-discharge"),
            ("CRAT_ERA5C_RAW_CAUSE_LEDGER", "off"),
        ],
    );
    assert!(off.is_empty(), "{off:?}");
}

/// W67b: bst with its driver restored and A1 off (015's variant): `main_0`'s
/// `root` is refused ownership by the temporary finalization.
#[test]
fn e5c_w67_b_the_ledger_names_the_temporary_finalization() {
    let variant = "/home/p51lee/dev/.crat-scratch/era-5c/bst-main/lib-variant.rs";
    if !std::path::Path::new(variant).is_file() {
        eprintln!("variant absent; skipping");
        return;
    }
    let rows = w67_rows(
        &format!("file:{variant}"),
        &[("CRAT_ERA5C_RESEAT_A1", "off")],
    );
    let row = w67_row(&rows, "src::bst::main_0::_2@d0");
    assert_eq!(row[1], "both", "{row:?}");
    assert!(
        row[7].contains("own-assume[temporary-finalization]"),
        "{row:?}"
    );
}

/// W67c: a kind-equate partner. On buffer (the corpus), some Raw slot has no
/// commit of its own: its row names a partner, reached through `kind-equate`,
/// whose own row is `direct`.
#[test]
fn e5c_w67_c_the_ledger_names_a_kind_equate_partner() {
    let buffer = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/rs-crown-derived/buffer/lib.rs"
    );
    if !std::path::Path::new(buffer).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let rows = w67_rows(&format!("file:{buffer}"), &[]);
    let partnered = rows
        .iter()
        .find(|row| {
            row[3] != row[0]
                && row[6].contains("kind-equate")
                && rows
                    .iter()
                    .any(|partner| partner[0] == row[3] && partner[6] == "direct")
        })
        .unwrap_or_else(|| panic!("no kind-equate partner: {rows:?}"));
    assert_ne!(partnered[2], "none", "{partnered:?}");
}

/// W67d: a pointer joined at a phi with null. The null edge excludes nothing
/// (§29): the row names the allocation source and the ownership refusal.
#[test]
fn e5c_w67_d_a_phi_with_null_names_its_real_cause() {
    let rows = w67_rows("w67-shapes", &[]);
    let row = w67_row(&rows, "phi_null::_2@d0");
    assert_eq!(
        (row[2].as_str(), row[6].as_str()),
        ("eager:allocation-source", "direct"),
        "{row:?}"
    );
    assert!(row[7].starts_with("own-assume["), "{row:?}");
    assert!(
        rows.iter()
            .all(|row| !row[6].contains("null") && !row[8].contains("null")),
        "{rows:?}"
    );
}

/// W67e: the objective class. With temporaries' Ref weight withheld
/// (`CRAT_ERA5C_REF_WEIGHT_NAMED=on`), `del::_13` can be Ref and can own, and
/// the optimum still chooses Raw; under the frame's weights it is not Raw.
#[test]
fn e5c_w67_e_the_ledger_names_the_objective() {
    let rows = w67_rows("w67-shapes", &[("CRAT_ERA5C_REF_WEIGHT_NAMED", "on")]);
    let row = w67_row(&rows, "del::_13@d0");
    assert_eq!(
        (row[1].as_str(), row[2].as_str(), row[7].as_str()),
        ("objective", "none", "none"),
        "{row:?}"
    );
    let frame = w67_rows("w67-shapes", &[]);
    assert!(
        !frame.iter().any(|row| row[0] == "del::_13@d0"),
        "{frame:?}"
    );
}

/// W68 (R609-3): the W63 child's lines on `W68_SHAPES` with the lend on and the
/// two arms as given, plus the type route's debug rows.
fn w68_lines(arg_order: &str, type_route: &str) -> Vec<String> {
    w63_lines(
        "w68-shapes",
        &[
            ("CRAT_ERA5C_LEND", "on"),
            ("CRAT_ERA5C_ARG_ORDER", arg_order),
            ("CRAT_ERA5C_OVERLAP_TYPE_ROUTE", type_route),
        ],
    )
}

/// W68a: the argument-order premise, on the corpus's own shape: quadtree's
/// `insert_(tree, (*tree).root, point, key)` reads the container in the argument
/// list of the call that receives the lent reborrow of `*tree` (the read is an
/// argument copy E5C-3 defers to the call).
#[test]
fn e5c_w68_a_a_read_in_the_receiving_calls_arguments_precedes_the_reborrow() {
    if !std::path::Path::new(W66_QUADTREE).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let shape = format!("file:{W66_QUADTREE}");
    let lines = |arg_order: &str| {
        w63_lines(
            &shape,
            &[
                ("CRAT_ERA5C_LEND", "on"),
                ("CRAT_ERA5C_ARG_ORDER", arg_order),
                ("CRAT_ERA5C_OVERLAP_TYPE_ROUTE", "on"),
                ("CRAT_E5C_W63_MODEL_ONLY", "1"),
            ],
        )
    };
    let key = "src::src::quadtree::quadtree_insert::_1@d0";
    let red = lines("off");
    assert_eq!(w63_kind(&red, key), "raw", "RED: {red:?}");
    let on = lines("on");
    assert_ne!(w63_kind(&on, key), "raw", "{on:?}");
    assert_ne!(
        w63_kind(&on, "src::src::quadtree::quadtree_insert::_23@d0"),
        "raw",
        "{on:?}"
    );
}

/// W68b: the type route. `reset_`'s `tree_t` and `node_t` formals are A5 overlap
/// partners; a store through `tree` while the reborrow of `node` is live is not
/// an argument of the receiving call, so only the type route clears it.
#[test]
fn e5c_w68_b_incompatible_pointees_are_not_overlap_partners() {
    let red = w68_lines("on", "off");
    assert_ne!(w63_kind(&red, "reset_::_2@d0"), "ref", "RED: {red:?}");
    assert!(!red.iter().any(|l| l.starts_with("a5-receipt ")), "{red:?}");
    let on = w68_lines("on", "on");
    assert_eq!(w63_kind(&on, "reset_::_2@d0"), "ref", "{on:?}");
    assert!(
        on.iter()
            .any(|l| l.starts_with("a5-receipt a5_type_disjoint_pairs=")),
        "{on:?}"
    );
}

/// W68c: the control. `same_`'s two formals share one type: the route gives
/// nothing and the conflict stays.
#[test]
fn e5c_w68_c_one_type_keeps_its_overlap_partner() {
    let on = w68_lines("on", "on");
    assert_ne!(w63_kind(&on, "same_::_2@d0"), "ref", "{on:?}");
}

/// The zero law's market (R645-2, era-5c 086), compile-only: every call from a
/// local function to a local function whose raw-pointer formal receives the
/// address of a place (a call-argument temporary defined once by `&mut place`,
/// `&place`, `&raw mut place` or `&raw const place`). One line per pair:
/// `E5C_PEEL caller callee formal-slot pointee-type place`.
#[test]
#[ignore = "the zero law's market probe, run on a named source"]
fn e5c_inner_ref_peel_market() {
    use rustc_data_structures::fx::FxHashMap;
    use rustc_middle::mir::{Rvalue, StatementKind, TerminatorKind};
    let path = std::env::var("CRAT_E5C_SIDE_SOURCE").expect("CRAT_E5C_SIDE_SOURCE");
    let source = std::fs::read_to_string(&path).expect("source");
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let mut functions = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            if let ItemKind::Fn { .. } = item.kind {
                functions.push(item.owner_id.def_id);
            }
        }
        let local: rustc_data_structures::fx::FxHashSet<_> =
            functions.iter().map(|f| f.to_def_id()).collect();
        let (mut calls, mut pairs) = (0usize, 0usize);
        for &caller in &functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
            let mut defs: FxHashMap<Local, (usize, Option<String>)> = FxHashMap::default();
            for block in body.basic_blocks.iter() {
                for statement in &block.statements {
                    if let StatementKind::Assign(assign) = &statement.kind
                        && let Some(lhs) = assign.0.as_local()
                    {
                        let entry = defs.entry(lhs).or_insert((0, None));
                        entry.0 += 1;
                        entry.1 = match &assign.1 {
                            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                                Some(format!("{place:?}"))
                            }
                            _ => None,
                        };
                    }
                }
            }
            for block in body.basic_blocks.iter() {
                let TerminatorKind::Call { func, args, .. } = &block.terminator().kind else {
                    continue;
                };
                let Some((callee, _)) = func.const_fn_def() else { continue };
                if !local.contains(&callee) {
                    continue;
                }
                calls += 1;
                let inputs = tcx.fn_sig(callee).skip_binder().skip_binder().inputs();
                for (index, arg) in args.iter().enumerate() {
                    let Some(proxy) = arg.node.place().and_then(|p| p.as_local()) else {
                        continue;
                    };
                    let Some((1, Some(place))) = defs.get(&proxy) else { continue };
                    let Some(formal_ty) = inputs.get(index) else { continue };
                    let rustc_middle::ty::TyKind::RawPtr(pointee, _) = formal_ty.kind() else {
                        continue;
                    };
                    pairs += 1;
                    println!(
                        "E5C_PEEL\t{}\t{}\t{}::_{}@d0\t{pointee}\t{place}",
                        tcx.def_path_str(caller),
                        tcx.def_path_str(callee),
                        tcx.def_path_str(callee),
                        index + 1
                    );
                }
            }
        }
        println!("E5C_PEEL_STATS calls={calls} pairs={pairs}");
    })
    .unwrap();
}

/// lil's no-ref-carrier losses (R645-3, era-5c 088), construction only: the
/// emission-time exclusions of a named source under the caller's arms, one
/// `E5C_EAGER kind slot` line each (`CRAT_ERA5C_EAGER_DUMP=on`). No solve.
#[test]
#[ignore = "the eager-exclusion dump, run on a named source"]
fn e5c_inner_eager_exclusions() {
    let path = std::env::var("CRAT_E5C_SIDE_SOURCE").expect("CRAT_E5C_SIDE_SOURCE");
    let source = std::fs::read_to_string(&path).expect("source");
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = super::crate_slots::CrateSlots::build(&program);
        let origins = super::origins::compute_origins(&program);
        let mutability = super::mutability_facts::MutFacts::from_program(&program);
        let solver = super::solver::KindSolver::new(&slots);
        super::construction::construct_bo_into(
            &program,
            &slots,
            &origins,
            &mutability,
            &solver,
            super::construction::CopyLendMode::Baseline,
        )
        .expect("the construction");
        eprintln!("E5C_EAGER_DONE");
    })
    .unwrap();
}

/// W71 (R659-1; the record `2026-09-29-retirement-fresh-and-interior-release-discharge.md`):
/// one program with a positive shape per discharge and the three controls. Each
/// conflict frame reads its formal, then calls a routed release, and does not
/// touch the formal again, so (α) never discharges.
const W71_SHAPES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case, unused_mut)]
extern "C" {
    fn malloc(_: u64) -> *mut core::ffi::c_void;
    fn free(_: *mut core::ffi::c_void);
    fn realloc(_: *mut core::ffi::c_void, _: u64) -> *mut core::ffi::c_void;
    fn exit(_: i32) -> !;
}
#[repr(C)] pub struct ctx_t { pub err: i32, pub msg: *mut i8, pub n: i32 }
#[repr(C)] pub struct env_t { pub parent: *mut env_t, pub name: *mut i8 }
#[repr(C)] pub struct stack_t { pub env: *mut env_t, pub depth: i32 }
#[repr(C)] pub struct z_t { pub sign: i32, pub used: u64, pub alloced: u64, pub chars: *mut u64 }
#[repr(C)] pub struct quad_t { pub w: [u64; 4] }
#[repr(C)] pub struct holder_t { pub q: *mut quad_t, pub buf: *mut u64 }
#[repr(C)] pub struct val_t { pub d: *mut i8, pub l: u64 }
// (γ): the released block is a local producer's, made below the conflict frame.
unsafe extern "C" fn make() -> *mut i8 { malloc(16) as *mut i8 }
unsafe extern "C" fn tmp_work() { let t = make(); *t = 1; free(t as *mut core::ffi::c_void); }
#[no_mangle] pub unsafe extern "C" fn run_step(c: *mut ctx_t) -> i32 { let n = (*c).n; tmp_work(); n }
// (α⁺): free-and-replace, the referent stored right after the release.
unsafe extern "C" fn set_error(c: *mut ctx_t) { free((*c).msg as *mut core::ffi::c_void); (*c).err = 1; (*c).msg = malloc(8) as *mut i8; }
#[no_mangle] pub unsafe extern "C" fn step(c: *mut ctx_t) -> i32 { let n = (*c).n; set_error(c); n }
// (α⁺), one frame up: the release in a callee that gets another pointer, the
// referent stored back in the caller (lil's `lil_pop_env`).
unsafe extern "C" fn free_env(e: *mut env_t) { free((*e).name as *mut core::ffi::c_void); free(e as *mut core::ffi::c_void); }
unsafe extern "C" fn pop_env(s: *mut stack_t) { let next = (*(*s).env).parent; free_env((*s).env); (*s).env = next; }
#[no_mangle] pub unsafe extern "C" fn leave(s: *mut stack_t) -> i32 { let d = (*s).depth; pop_env(s); d }
// (β′): u64 limbs against a struct with an `int`.
unsafe extern "C" fn zfree(a: *mut z_t) { free((*a).chars as *mut core::ffi::c_void); }
#[no_mangle] pub unsafe extern "C" fn zclear(a: *mut z_t) -> u64 { let u = (*a).used; zfree(a); u }
// Control: a genuine release of the referent itself.
unsafe extern "C" fn destroy(a: *mut z_t) { free(a as *mut core::ffi::c_void); }
#[no_mangle] pub unsafe extern "C" fn finish(a: *mut z_t) -> u64 { let u = (*a).used; destroy(a); u }
// Control: a P-only referent (four u64) against a released u64 block.
unsafe extern "C" fn drop_buf(h: *mut holder_t) { free((*h).buf as *mut core::ffi::c_void); }
#[no_mangle] pub unsafe extern "C" fn touch(q: *mut quad_t, h: *mut holder_t) -> u64 { let x = (*q).w[0]; drop_buf(h); x }
// STOP 2 (i): a possibly-zero-size `realloc` whose null path returns untouched.
unsafe extern "C" fn append(v: *mut val_t) -> i32 {
    let n = realloc((*v).d as *mut core::ffi::c_void, (*v).l.wrapping_add(2)) as *mut i8;
    if n.is_null() { return 0; }
    (*v).d = n; (*v).l = (*v).l.wrapping_add(1); 1
}
#[no_mangle] pub unsafe extern "C" fn push(v: *mut val_t) -> u64 { let l = (*v).l; append(v); l }
// W73 (R666-1): a callee that releases and then diverges never reaches the
// caller's later use; the same callee returning is the control.
unsafe extern "C" fn die(c: *mut ctx_t) { free((*c).msg as *mut core::ffi::c_void); exit(1); }
#[no_mangle] pub unsafe extern "C" fn fail(c: *mut ctx_t, bad: i32) -> i32 { if bad != 0 { die(c); } (*c).n }
unsafe extern "C" fn reset_msg(c: *mut ctx_t) { free((*c).msg as *mut core::ffi::c_void); }
#[no_mangle] pub unsafe extern "C" fn recover(c: *mut ctx_t, bad: i32) -> i32 { if bad != 0 { reset_msg(c); } (*c).n }
"#;

/// W71a: `ctx.rs` with a command callback that `lil_parse` dispatches while its
/// `lil` is live, registered as `fnc_jaileval` (a sub-interpreter made and freed).
const W71_CTX_JAIL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case, unused_mut)]
extern "C" { fn malloc(_: u64) -> *mut core::ffi::c_void; fn free(_: *mut core::ffi::c_void); }
#[repr(C)] pub struct env_t { pub parent: *mut env_t, pub depth: i32 }
pub type proc_t = Option<unsafe extern "C" fn(lil_t, i32) -> i32>;
#[repr(C)] pub struct ctx_t { pub code: *const u8, pub head: usize, pub clen: usize, pub ignoreeol: i32, pub env: *mut env_t, pub cmd: proc_t }
pub type lil_t = *mut ctx_t;
#[no_mangle] pub unsafe extern "C" fn lil_new() -> lil_t {
    let mut lil = malloc(core::mem::size_of::<ctx_t>() as u64) as lil_t;
    (*lil).code = 0 as *const u8; (*lil).head = 0; (*lil).clen = 0; (*lil).ignoreeol = 0; (*lil).cmd = None;
    (*lil).env = malloc(core::mem::size_of::<env_t>() as u64) as *mut env_t;
    (*(*lil).env).parent = 0 as *mut env_t; (*(*lil).env).depth = 0;
    return lil;
}
unsafe extern "C" fn ateol(mut lil: lil_t) -> i32 {
    return ((*lil).ignoreeol == 0 && *((*lil).code).offset((*lil).head as isize) == b'\n') as i32;
}
unsafe extern "C" fn skip_spaces(mut lil: lil_t) {
    while (*lil).head < (*lil).clen && *((*lil).code).offset((*lil).head as isize) == b' ' {
        if ateol(lil) != 0 { break; }
        (*lil).head = (*lil).head.wrapping_add(1);
    }
}
#[no_mangle] pub unsafe extern "C" fn lil_push_env(mut lil: lil_t) -> *mut env_t {
    let mut env = malloc(core::mem::size_of::<env_t>() as u64) as *mut env_t;
    (*env).parent = (*lil).env; (*env).depth = 1; (*lil).env = env;
    return env;
}
#[no_mangle] pub unsafe extern "C" fn lil_pop_env(mut lil: lil_t) {
    let mut env = (*lil).env;
    if !(*env).parent.is_null() { (*lil).env = (*env).parent; free(env as *mut core::ffi::c_void); }
}
#[no_mangle] pub unsafe extern "C" fn lil_parse(mut lil: lil_t, mut code: *const u8, mut len: usize) -> i32 {
    let save = (*lil).code; (*lil).code = code; (*lil).clen = len; (*lil).head = 0;
    lil_push_env(lil);
    skip_spaces(lil);
    if let Some(f) = (*lil).cmd { f(lil, 0); }
    let r = ateol(lil);
    lil_pop_env(lil);
    (*lil).code = save;
    return r;
}
#[no_mangle] pub unsafe extern "C" fn lil_free(mut lil: lil_t) {
    if lil.is_null() { return; }
    free((*lil).env as *mut core::ffi::c_void);
    free(lil as *mut core::ffi::c_void);
}
#[no_mangle] pub unsafe extern "C" fn lil_register(mut lil: lil_t, mut f: proc_t) { (*lil).cmd = f; }
unsafe extern "C" fn fnc_jaileval(mut lil: lil_t, mut x: i32) -> i32 {
    let mut sublil = lil_new();
    let r = lil_parse(sublil, (*lil).code, (*lil).clen);
    lil_free(sublil);
    return r;
}
#[no_mangle] pub unsafe extern "C" fn run(code: *const u8, len: usize) -> i32 {
    let mut lil = lil_new();
    lil_register(lil, Some(fnc_jaileval));
    let r = lil_parse(lil, code, len);
    lil_free(lil);
    return r;
}
"#;

/// W71's lines: the W63 child's receipts (`discharge …`, `retire-conflict …`)
/// and model, under L01¹⁰'s arms with the three switches set to `on` / `off`.
fn w71_lines(shape: &str, on: &str, extra: &[(&str, &str)]) -> Vec<String> {
    let mut env: Vec<(&str, &str)> = vec![
        ("CRAT_ERA5C_LEND", "on"),
        ("CRAT_ERA5C_RETIRE_FRESH", on),
        ("CRAT_ERA5C_RETIRE_ROUTE_USE", on),
        ("CRAT_ERA5C_TYPED_SOLE", on),
    ];
    env.extend_from_slice(extra);
    w63_lines(shape, &env)
}

fn w71_has(lines: &[String], prefix: &str, target: &str, needle: &str) -> bool {
    lines
        .iter()
        .any(|l| l.starts_with(prefix) && l.contains(target) && l.contains(needle))
}

/// W71 (b, c, d, the controls, g): each discharge on its shape, off vs on; each
/// fault takes its GREEN away; the controls and the zero-size path stay conflicts.
#[test]
fn e5c_w71_the_three_discharges_and_their_controls() {
    let off = w71_lines("w71-shapes", "off", &[]);
    let on = w71_lines("w71-shapes", "on", &[]);
    // A crate-root function's slot key is `<f>::_<n>@d<k>`. A held conflict
    // frame's formal is not Ref in the accepted model (the final review lists
    // no conflict: its target is already committed).
    let conflict = |lines: &[String], f: &str| w63_kind(lines, &format!("{f}::_1@d0")) != "ref";
    let receipt = |lines: &[String], f: &str, rule: &str| {
        w71_has(lines, "discharge", &format!("target={f}::_1@d0"), rule)
    };
    // RED: at L01¹⁰ every conflict frame is held.
    for f in [
        "run_step", "step", "leave", "zclear", "finish", "touch", "push",
    ] {
        assert!(conflict(&off, f), "RED {f}: {off:?}");
    }
    for f in ["run_step", "step", "leave", "zclear"] {
        assert!(!conflict(&on, f), "GREEN {f}: {on:?}");
    }
    // GREEN.
    assert!(receipt(&on, "run_step", "fresh-in-route"), "(γ) {on:?}");
    assert!(
        receipt(&on, "step", "post-release-use-route"),
        "(α⁺) {on:?}"
    );
    assert!(
        receipt(&on, "leave", "post-release-use-route"),
        "(α⁺) one frame up {on:?}"
    );
    assert!(
        receipt(&on, "zclear", "containment=sole-type"),
        "(β′) {on:?}"
    );
    // The controls and STOP 2 (i).
    for f in ["finish", "touch", "push"] {
        assert!(conflict(&on, f), "control {f}: {on:?}");
        assert!(!receipt(&on, f, ""), "control {f}: {on:?}");
    }
    // The faults.
    for (fault, f, rule) in [
        ("no-fresh", "run_step", "fresh-in-route"),
        ("no-route-use", "step", "post-release-use-route"),
        ("no-sole", "zclear", "containment=sole-type"),
    ] {
        let lines = w71_lines("w71-shapes", "on", &[("CRAT_E5C_W71_FAULT", fault)]);
        assert!(
            !receipt(&lines, f, rule),
            "fault {fault} must be caught: {lines:?}"
        );
    }
}

/// W71a: lil's shape. Does the review raise the context formals' conflict on
/// the jail's release, and does (γ) discharge it through the callback's route?
/// Measured (era-5c 097): on this reduction the review raises none -- the
/// jail's `env_t` release is (β)'s at L01¹⁰ and the sub-interpreter's own
/// release is no conflict -- so the context formal is Ref in both arms; lil's
/// held formals are measured on the solve.
#[test]
fn e5c_w71_a_the_jail_release_is_fresh() {
    let off = w71_lines("ctx-jail", "off", &[]);
    let on = w71_lines("ctx-jail", "on", &[]);
    let jail = |lines: &[String]| {
        lines
            .iter()
            .filter(|l| l.contains("lil_free") || l.contains("jaileval"))
            .cloned()
            .collect::<Vec<_>>()
    };
    eprintln!("W71a off {:?}\nW71a on {:?}", jail(&off), jail(&on));
    assert_eq!(w63_kind(&off, "fnc_jaileval::_1@d0"), "ref", "{off:?}");
    assert_eq!(w63_kind(&on, "fnc_jaileval::_1@d0"), "ref", "{on:?}");
}

/// W72 (R659-1; wave-5d 133 STOP 2): the arm-(a) receipt export. On quadtree's
/// own `insert_(tree, (*tree).root, …)` the model's receipts equal the portable
/// export's and the prepared entry's, and one names `quadtree_insert`'s call
/// with the tree as its lent pointer; with the arm off the family is not recorded.
#[test]
fn e5c_w72_the_arg_order_receipts_reach_the_entry() {
    if !std::path::Path::new(W66_QUADTREE).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let shape = format!("file:{W66_QUADTREE}");
    let lines = |arg_order: &str| {
        w63_lines(
            &shape,
            &[
                ("CRAT_ERA5C_LEND", "on"),
                ("CRAT_ERA5C_ARG_ORDER", arg_order),
                ("CRAT_ERA5C_OVERLAP_TYPE_ROUTE", "on"),
                ("CRAT_E5C_W72", "1"),
            ],
        )
    };
    let on = lines("on");
    let summary = on
        .iter()
        .find(|l| l.starts_with("arg-order model="))
        .unwrap_or_else(|| panic!("{on:?}"));
    assert!(summary.ends_with("equal=true"), "{summary}");
    assert!(
        on.iter().any(|l| l.starts_with("arg-order-row ")
            && l.contains("quadtree_insert")
            && l.contains("lent=_1 ")),
        "{on:?}"
    );
    // R666-1, the loader: the key's span is the receiving call's own text.
    assert!(
        on.iter().any(|l| l.starts_with("arg-order-hoist ")
            && l.contains("quadtree_insert")
            && l.contains("lent=_1 ")
            && l.contains("text=insert_(")
            && l.contains(".root")),
        "{on:?}"
    );
    let off = lines("off");
    let summary = off
        .iter()
        .find(|l| l.starts_with("arg-order model="))
        .unwrap_or_else(|| panic!("{off:?}"));
    assert!(
        summary.starts_with("arg-order model=none") && summary.contains("not recorded"),
        "{summary}"
    );
}

/// W73 (R666-1): (α) discharges only when every route frame below returns. At
/// L01¹⁰ `fail`'s later use discharges `die`'s release although `die` exits
/// after it (RED); with `CRAT_ERA5C_ALPHA_RETURNS` it stays a conflict, while
/// `recover` (a returning callee) keeps its discharge; the fault gives it back.
#[test]
fn e5c_w73_alpha_needs_the_route_to_return() {
    let run = |alpha: &str, fault: Option<&str>| {
        let mut extra = vec![("CRAT_ERA5C_ALPHA_RETURNS", alpha)];
        if let Some(fault) = fault {
            extra.push(("CRAT_E5C_W71_FAULT", fault));
        }
        w71_lines("w71-shapes", "off", &extra)
    };
    let alpha = |lines: &[String], f: &str| {
        w71_has(
            lines,
            "discharge",
            &format!("target={f}::"),
            "post-free-use(",
        )
    };
    let off = run("off", None);
    assert!(alpha(&off, "fail"), "RED: {off:?}");
    assert!(alpha(&off, "recover"), "{off:?}");
    let on = run("on", None);
    assert!(!alpha(&on, "fail"), "{on:?}");
    assert_ne!(w63_kind(&on, "fail::_1@d0"), "ref", "{on:?}");
    assert!(
        alpha(&on, "recover"),
        "the control keeps its discharge: {on:?}"
    );
    let fault = run("on", Some("no-alpha-returns"));
    assert!(alpha(&fault, "fail"), "the fault must be caught: {fault:?}");
}

/// W74 (R668-4; analysis-fanout 014 STOP 1 (i)): the ledger names each Mode-A
/// commit's witnessed clause. `g`: `p` lends `(*s).x`, `q` copies it, and a
/// write through `r`, a Raw copy of `s` (cast to an integer), invalidates the
/// loan while `q` is live -- the commit falls on `q` with `p` its Ref peer and
/// `r` its Raw invalidator. `h`: `p` is its own loan's issuer and only live
/// requirer -- self-issued.
const W74_SHAPES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case, unused_mut, unused_assignments)]
#[repr(C)] pub struct S { pub x: i32 }
#[no_mangle] pub unsafe extern "C" fn g(s: *mut S) -> i32 {
    let r: *mut S = s;
    let n = r as usize;
    let p: *mut i32 = &mut (*s).x;
    let q: *mut i32 = p;
    (*r).x = 5;
    *q + n as i32
}
#[no_mangle] pub unsafe extern "C" fn h(a: *mut i32) -> i32 {
    let p: *mut i32 = a;
    *a = 1;
    *p
}
"#;

/// W74: the ledger's clause columns (`tsv` 9–11: `noref_clause`,
/// `noref_ref_peers`, `noref_raw_invalidators`). A Mode-A first cause names its
/// commit's clause; any other names none. `CRAT_E5C_W74_FAULT=no-invalidators`
/// (test builds) drops the recorded invalidators: RED.
#[test]
fn e5c_w74_the_ledger_names_each_commits_clause() {
    let rows = w67_rows("w74-shapes", &[]);
    let mode_a = [
        "borrow-exclusion",
        "retirement-conflict",
        "reader-obligation",
    ];
    for row in &rows {
        let clause = row[9].as_str();
        if mode_a.contains(&row[2].as_str()) {
            assert!(clause == "guarded" || clause == "self-issued", "{row:?}");
        } else {
            assert_eq!(
                (clause, &row[10][..], &row[11][..]),
                ("-", "-", "-"),
                "{row:?}"
            );
        }
    }
    let guarded = rows
        .iter()
        .find(|row| row[3].starts_with("g::") && row[9] == "guarded")
        .unwrap_or_else(|| panic!("no guarded commit in g: {rows:?}"));
    assert_eq!(
        guarded[10], guarded[5],
        "the Ref peer is the issuer: {guarded:?}"
    );
    // `r`'s write invalidates in round 1, while `r` is still Ref; the round-2
    // commit lists the round-1 target as its Raw invalidator.
    assert!(
        rows.iter()
            .any(|row| row[3].starts_with("g::") && row[11].starts_with("g::")),
        "a Raw invalidator: {rows:?}"
    );
    let own = rows
        .iter()
        .find(|row| row[3].starts_with("h::") && row[9] == "self-issued")
        .unwrap_or_else(|| panic!("no self-issued commit in h: {rows:?}"));
    assert_eq!(own[10], "-", "{own:?}");
    let fault = w67_rows("w74-shapes", &[("CRAT_E5C_W74_FAULT", "no-invalidators")]);
    assert!(
        fault.iter().all(|row| row[11] == "-"),
        "the fault must be caught: {fault:?}"
    );
}

/// W69 (R617-1): the W63 child under the guarded repair with the L2 diagnostics on -- its lines,
/// and the planner's `[bo-l2]` lines prefixed `l2 `.
fn w69_lines(shape: &str, extra: &[(&str, &str)]) -> Vec<String> {
    let mut env: Vec<(&str, &str)> = vec![
        ("CRAT_ERA5C_LEND", "on"),
        ("CRAT_BO_REPAIR", "guarded"),
        ("CRAT_POINTER_DECISION_DIAGNOSTICS", "raw"),
    ];
    env.extend_from_slice(extra);
    w63_child(shape, &env)
        .lines()
        .filter_map(|l| {
            l.find("E5C_W63 ")
                .map(|i| l[i + 8..].to_owned())
                .or_else(|| l.find("E5C_MODEL ").map(|i| l[i + 10..].to_owned()))
                .or_else(|| l.find("[bo-l2] ").map(|i| format!("l2 {}", &l[i + 8..])))
        })
        .collect()
}

fn w69_model(lines: &[String]) -> Vec<&String> {
    lines
        .iter()
        .filter(|l| {
            !l.starts_with("l2 ")
                && !l.starts_with("repair-receipt ")
                && !l.starts_with("residuals ")
                && !l.starts_with("validate ")
                && !l.starts_with("lendable ")
                && !l.starts_with("waiver ")
                && !l.starts_with("discharge ")
                && !l.starts_with("retire-conflict ")
                && !l.starts_with("a5-receipt ")
                && !l.starts_with("ledger ")
        })
        .collect()
}

/// W69a's solve: one fixture under one repair mode, in process (NB5-L's S7 harness). The Ref
/// count, the stats, and whether the accepted model is a Mode-A fixpoint (`model_accepts`).
fn w69_solve(
    code: &str,
    mode: super::borrow_verify::RepairMode,
) -> (usize, super::borrow_verify::RoundStats, bool) {
    use rustc_hir::{ItemKind, OwnerNode};
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let mut functions = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            if let ItemKind::Fn { .. } = item.kind {
                functions.push(item.owner_id.def_id);
            }
        }
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs: Vec::new(),
        };
        let slots = super::crate_slots::CrateSlots::build(&program);
        let crate_ctxt = super::CrateCtxt::new(&program);
        let solver = super::solver::KindSolver::new(&slots);
        let (_emission, selectors) = super::emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &super::origins::compute_origins(&program),
            &solver,
        )
        .expect("emit");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            super::coherence::add_coherence(&solver, &slots, g, &body);
        }
        let (model, stats) = super::borrow_verify::RepairMode::with_override(mode, || {
            super::borrow_verify::verify_to_fixpoint_counting(
                &program, &slots, &solver, &selectors, true,
            )
        });
        let model = model.expect("the fixture accepts");
        let accepts = super::borrow_verify::model_accepts(&program, &slots, &model, true);
        let refs = model
            .values()
            .filter(|kind| **kind == super::SlotKind::Ref)
            .count();
        (refs, stats, accepts)
    })
    .unwrap()
}

/// NB5-L2's natural accumulation over-pin (`nb5l2_probe_finds_natural_accumulation_overpin`).
const W69_CASCADE: &str = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
    unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";

/// W69b's search (R617-1): shapes under both repairs, one line each; with the diagnostics switch the
/// planner's `[bo-l2]` lines name any recurrence escalation.
#[test]
#[ignore = "the search for W69b's escalation shape"]
fn e5c_inner_w69_search() {
    use super::borrow_verify::RepairMode;
    let fan_out = |n: usize| {
        let aliases: String = (0..n).map(|i| format!("let a{i} = id(x); ")).collect();
        let uses: String = (0..n).map(|i| format!("*a{i} + ")).collect();
        format!(
            "unsafe fn id(p: *mut i32) -> *mut i32 {{ p }} \
             unsafe fn f(p: *mut i32) -> i32 {{ let bb = p; let x = id(p); {aliases}*bb = 5; {uses}*x }}"
        )
    };
    let shapes: Vec<(&str, String)> = vec![
        ("cascade", W69_CASCADE.to_owned()),
        (
            "two_requirer",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let base = id(p); let a = id(base); let b = id(base); \
             let w = p; *w = 9; *a + *b }"
                .to_owned(),
        ),
        (
            "three_requirer",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let bb = p; let x = id(p); let z = id(x); let q = id(x); \
             *bb = 5; *x + *z + *q }"
                .to_owned(),
        ),
        (
            "asymmetric",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let a = id(p); let b = id(p); let d = id(b); \
             *a = 1; *b = 2; *d = 3; let w = p; *w = 4; *a + *b + *d }"
                .to_owned(),
        ),
        (
            "chain",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let a = id(p); let b = id(a); let c = id(b); \
             *c = 1; *b = 2; *a = 3; let w = p; *w = 4; *a + *b + *c }"
                .to_owned(),
        ),
        (
            "crossed",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32, q: *mut i32) -> i32 { let a = id(p); let b = id(q); \
             let c = id(a); *b = 1; *a = 2; let d = id(b); *c = 3; *d = 4; *p = 5; *q = 6; *a + *b + *c + *d }"
                .to_owned(),
        ),
        ("fan_out_8", fan_out(8)),
        ("fan_out_33", fan_out(32)),
        // L01¹² (R677-4): W69b's candidates -- the issuer peer satisfies `¬ref` by
        // owning (a later `free`), and an owning slot's loans stay in the replay.
        (
            "owning_peer",
            "extern \"C\" { fn malloc(_: u64) -> *mut core::ffi::c_void; fn free(_: *mut core::ffi::c_void); } \
             unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f() -> i32 { let p = malloc(4) as *mut i32; let a = id(p); let c = id(a); \
             *p = 5; let r = *c; free(a as *mut core::ffi::c_void); r }"
                .to_owned(),
        ),
        (
            "owning_peer_direct",
            "extern \"C\" { fn malloc(_: u64) -> *mut core::ffi::c_void; fn free(_: *mut core::ffi::c_void); } \
             unsafe fn f() -> i32 { let p = malloc(4) as *mut i32; let a = p; let c = a; \
             *p = 5; let r = *c; free(a as *mut core::ffi::c_void); r }"
                .to_owned(),
        ),
    ];
    for (name, code) in &shapes {
        eprintln!("E5C_W69S begin {name}");
        let (mode_a, mode_a_stats, _) = w69_solve(code, RepairMode::ModeA);
        let (refs, stats, accepts) = w69_solve(code, RepairMode::Guarded);
        eprintln!(
            "E5C_W69S {name} guarded_refs={refs} mode_a_refs={mode_a} rounds={}/{} commits={}/{} \
             fallback={:?} accepts={accepts}",
            stats.rounds,
            mode_a_stats.rounds,
            stats.commits_conflict,
            mode_a_stats.commits_conflict,
            stats.guarded_fallback
        );
    }
}

/// W69a: a guarded round lifts Mode-A's over-pin. On the cascade Mode-A commits two `¬ref`s and
/// the first is unnecessary once the second holds; the guarded clause on the first deactivates
/// when its peer moves, so the guarded model keeps more Ref, accepts without falling back, and is
/// a fixpoint of the Mode-A replay.
#[test]
fn e5c_w69_a_a_guarded_round_lifts_a_mode_a_over_pin() {
    use super::borrow_verify::RepairMode;
    let (mode_a, mode_a_stats, _) = w69_solve(W69_CASCADE, RepairMode::ModeA);
    let (guarded, stats, accepts) = w69_solve(W69_CASCADE, RepairMode::Guarded);
    assert_eq!(stats.repair, RepairMode::Guarded);
    assert_eq!(stats.guarded_fallback, None, "{stats:?}");
    assert!(
        accepts,
        "the guarded model must be a fixpoint of the replay"
    );
    assert!(
        guarded > mode_a,
        "RED: the guarded run keeps no more Ref than Mode-A ({guarded} vs {mode_a}); \
         {stats:?} vs {mode_a_stats:?}"
    );
}

/// W69c: an A5 overlap pair is in the guarded replay's context. `same_`'s two formals share one type
/// (W68c's effective pair). Before the port the dispatch refused A5 in the L2 loop (a panic); the
/// guarded run accepts without falling back, and the conflict met through the partner carries the
/// mark in its hazard key. Fault `no-a5-context`: the mark is gone.
#[test]
fn e5c_w69_c_an_a5_pair_is_in_the_guarded_witness_context() {
    let on = w69_lines("w68-shapes", &[]);
    assert!(
        on.contains(&"repair-receipt repair=guarded".to_owned()),
        "{on:?}"
    );
    assert!(
        on.contains(&"repair-receipt guarded_fallbacks=0".to_owned()),
        "{on:?}"
    );
    let marked = |lines: &[String]| {
        lines
            .iter()
            .any(|l| l.starts_with("l2 event=guarded_hazard") && l.contains("~partner:"))
    };
    assert!(marked(&on), "{on:?}");
    let fault = w69_lines("w68-shapes", &[("CRAT_E5C_W69_FAULT", "no-a5-context")]);
    assert!(!marked(&fault), "the fault must be caught: {fault:?}");
}

/// W69d: a guarded accept records the residual certificate, the rows Mode-A records on the same
/// model (the separate loop left it `None`). Fault `no-certificate`: `none`.
#[test]
fn e5c_w69_d_a_guarded_accept_records_the_residual_certificate() {
    let guarded = w69_lines("w68-shapes", &[]);
    let mode_a = w63_lines("w68-shapes", &[("CRAT_ERA5C_LEND", "on")]);
    assert_ne!(w63_kind(&guarded, "residuals"), "none", "{guarded:?}");
    if w69_model(&guarded) == w69_model(&mode_a) {
        assert_eq!(
            w63_kind(&guarded, "residuals"),
            w63_kind(&mode_a, "residuals")
        );
    }
    let fault = w69_lines("w68-shapes", &[("CRAT_E5C_W69_FAULT", "no-certificate")]);
    assert_eq!(
        w63_kind(&fault, "residuals"),
        "none",
        "the fault must be caught"
    );
}

/// W69e: the field-own branch (relay 117) runs under the guarded repair. avl's rotations leave a
/// residual on an Owning field (W56); the separate loop declined it; the one loop repairs it before
/// the mode arm, so the guarded run accepts without falling back. Fault `no-field-own`: the guarded
/// run declines and the program falls back to Mode-A, which the receipt names.
#[test]
fn e5c_w69_e_the_field_own_branch_runs_under_the_guarded_repair() {
    let run = |fault: Option<&str>| -> Vec<String> {
        let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
        env.push(("CRAT_ERA5C_MUT_MODEL", "on"));
        env.push(("CRAT_ERA5C_DEREF_READER", "on"));
        env.push(("CRAT_ERA5C_FIELD_OWN_REPAIR", "on"));
        env.push(("CRAT_E5C_SHAPE", "AVL"));
        env.push(("CRAT_BO_REPAIR", "guarded"));
        if let Some(fault) = fault {
            env.push(("CRAT_E5C_W69_FAULT", fault));
        }
        child(
            "analyses::borrow_ownership::null_paths_tests::e5c_inner_shape_decline_reason",
            &env,
        )
        .lines()
        .filter_map(|l| {
            l.find("E5C_DECLINE ")
                .map(|i| l[i..].to_owned())
                .or_else(|| l.find("E5C_REPAIR ").map(|i| l[i..].to_owned()))
        })
        .collect()
    };
    let on = run(None);
    assert!(on.contains(&"E5C_DECLINE none".to_owned()), "{on:?}");
    assert!(
        on.contains(&"E5C_REPAIR repair=guarded".to_owned()),
        "{on:?}"
    );
    let fault = run(Some("no-field-own"));
    assert!(
        fault.contains(&"E5C_REPAIR repair=guarded->mode-a".to_owned()),
        "the fault must be caught: {fault:?}"
    );
    assert!(
        fault
            .iter()
            .any(|l| l.starts_with("E5C_REPAIR guarded_fallback_reasons=field-conflict")),
        "{fault:?}"
    );
}

/// W75 (R677-4; era-5c 100a STOP 1): libtree's `string_table_maybe_grow` shape.
/// `grow` reallocs `(*t).arr` to a computed size and exits on null; `grow16`
/// reallocs to the constant 16. `store` / `store16` use `*t` after the call.
const W75_SHAPES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case, unused_mut)]
extern "C" {
    fn realloc(_: *mut core::ffi::c_void, _: u64) -> *mut core::ffi::c_void;
    fn exit(_: i32) -> !;
}
#[repr(C)] pub struct tab { pub n: u64, pub cap: u64, pub arr: *mut i8 }
unsafe extern "C" fn grow(t: *mut tab, k: u64) {
    if (*t).n.wrapping_add(k) <= (*t).cap { return; }
    (*t).cap = 2u64.wrapping_mul((*t).n.wrapping_add(k));
    let a = realloc((*t).arr as *mut core::ffi::c_void, (*t).cap) as *mut i8;
    if a.is_null() { exit(1); }
    (*t).arr = a;
}
#[no_mangle] pub unsafe extern "C" fn store(t: *mut tab, k: u64) -> u64 {
    grow(t, k);
    (*t).n = (*t).n.wrapping_add(k);
    (*t).n
}
unsafe extern "C" fn grow16(t: *mut tab) {
    let a = realloc((*t).arr as *mut core::ffi::c_void, 16) as *mut i8;
    if a.is_null() { exit(1); }
    (*t).arr = a;
}
#[no_mangle] pub unsafe extern "C" fn store16(t: *mut tab) -> u64 {
    grow16(t);
    (*t).n
}
"#;

/// W75: with (α)'s route condition (`CRAT_ERA5C_ALPHA_RETURNS`) the exit path
/// removes `store`'s and `store16`'s (α) discharges (RED). With
/// `CRAT_ERA5C_REALLOC_REFUTE` the constant size's null branch is refuted --
/// `store16` and `grow16`'s own frame discharge -- while the computed size is
/// not; the zero-size premise (`CRAT_ERA5C_REALLOC_NONZERO`) refutes both; the
/// fault `no-refute` gives the RED back. Without the route condition both
/// discharge (L01¹⁰'s control).
#[test]
fn e5c_w75_alpha_route_refutes_the_realloc_null_path() {
    let run = |extra: &[(&str, &str)]| {
        let mut env = vec![("CRAT_ERA5C_ALPHA_RETURNS", "on")];
        env.extend_from_slice(extra);
        w71_lines("w75-shapes", "off", &env)
    };
    let alpha = |lines: &[String], f: &str| {
        w71_has(
            lines,
            "discharge",
            &format!("target={f}::_1@d0"),
            "post-free-use(",
        )
    };
    let red = run(&[]);
    assert!(
        !alpha(&red, "store") && !alpha(&red, "store16"),
        "RED: {red:?}"
    );
    let on = run(&[("CRAT_ERA5C_REALLOC_REFUTE", "on")]);
    assert!(alpha(&on, "store16"), "{on:?}");
    assert!(
        alpha(&on, "grow16"),
        "the releasing frame's own window: {on:?}"
    );
    assert!(
        !alpha(&on, "store"),
        "a computed size is not refuted: {on:?}"
    );
    let premise = run(&[
        ("CRAT_ERA5C_REALLOC_REFUTE", "on"),
        ("CRAT_ERA5C_REALLOC_NONZERO", "on"),
    ]);
    assert!(
        alpha(&premise, "store") && alpha(&premise, "store16"),
        "{premise:?}"
    );
    let fault = run(&[
        ("CRAT_ERA5C_REALLOC_REFUTE", "on"),
        ("CRAT_ERA5C_REALLOC_NONZERO", "on"),
        ("CRAT_E5C_W71_FAULT", "no-refute"),
    ]);
    assert!(
        !alpha(&fault, "store16"),
        "the fault must be caught: {fault:?}"
    );
    let l10 = w71_lines("w75-shapes", "off", &[("CRAT_ERA5C_ALPHA_RETURNS", "off")]);
    assert!(alpha(&l10, "store") && alpha(&l10, "store16"), "{l10:?}");
}

/// W78 (R682-3): a discharge only the zero-size `realloc` premise admits is
/// receipted `premise=realloc-nonzero@R684-1` (R686-4). On W75's shapes with the premise on,
/// `store`'s (computed size) receipt carries it; `store16`'s and `grow16`'s
/// (constant size) do not; without the premise no receipt does; the fault
/// `no-premise` keeps the discharge and drops the marker.
#[test]
fn e5c_w78_the_realloc_premise_is_receipted() {
    let run = |extra: &[(&str, &str)]| {
        let mut env = vec![
            ("CRAT_ERA5C_ALPHA_RETURNS", "on"),
            ("CRAT_ERA5C_REALLOC_REFUTE", "on"),
        ];
        env.extend_from_slice(extra);
        w71_lines("w75-shapes", "off", &env)
    };
    let marked = |lines: &[String], f: &str| {
        w71_has(
            lines,
            "discharge",
            &format!("target={f}::_1@d0"),
            "premise=realloc-nonzero@R684-1)",
        )
    };
    let discharged =
        |lines: &[String], f: &str| w71_has(lines, "discharge", &format!("target={f}::_1@d0"), "");
    let premise = run(&[("CRAT_ERA5C_REALLOC_NONZERO", "on")]);
    assert!(marked(&premise, "store"), "{premise:?}");
    assert!(
        discharged(&premise, "store16") && !marked(&premise, "store16"),
        "{premise:?}"
    );
    assert!(
        discharged(&premise, "grow16") && !marked(&premise, "grow16"),
        "{premise:?}"
    );
    let strict = run(&[]);
    assert!(
        !strict.iter().any(|l| l.contains("premise=realloc-nonzero")),
        "{strict:?}"
    );
    let fault = run(&[
        ("CRAT_ERA5C_REALLOC_NONZERO", "on"),
        ("CRAT_E5C_W71_FAULT", "no-premise"),
    ]);
    assert!(
        discharged(&fault, "store") && !marked(&fault, "store"),
        "the fault must be caught: {fault:?}"
    );
}

/// W79 (R690-6; analysis-fanout 018): tisp's `mk_list(st, n, ...)`. A call argument
/// past a C-variadic callee's fixed parameters has no parameter local, so it is not
/// bound as a loan on the callee's body local `_(i+1)`: before, the portable export
/// refused the program ("unresolved callee argument: mk_list argument 4 of 3").
const W79_SHAPES: &str = r#"
#![feature(c_variadic)]
#![allow(dead_code, unused_mut, non_camel_case_types, unused_braces, unused_assignments)]
extern "C" { fn malloc(_: u64) -> *mut ::core::ffi::c_void; }
#[repr(C)] pub struct Val { pub x: i32, pub next: *mut Val }
// tisp's `mk_list(st, n, ...)` (analysis-fanout 018): its first body locals are pointers, so a call
// argument past the fixed parameters is read as a loan on the callee's body local `_(i+1)`.
#[no_mangle] pub unsafe extern "C" fn mk_list(mut st: *mut Val, mut n: i32, mut args: ...) -> *mut Val {
    let mut lst = ::core::ptr::null_mut::<Val>();
    let mut cur = ::core::ptr::null_mut::<Val>();
    let mut argp: ::core::ffi::VaListImpl;
    argp = args.clone();
    lst = argp.arg::<*mut Val>();
    cur = lst;
    (*cur).next = st;
    return lst;
}
#[no_mangle] pub unsafe extern "C" fn mk_pair(mut a: i32, mut next: *mut Val) -> *mut Val { let mut p = malloc(16) as *mut Val; (*p).x = a; (*p).next = next; return p; }
#[no_mangle] pub unsafe extern "C" fn caller(mut st: *mut Val, mut v: *mut Val) -> *mut Val {
    return { let __arg_2 = mk_pair(1, st); let __arg_4 = mk_pair(2, st); mk_list(st, 3, __arg_2, v, __arg_4) };
}
"#;

/// W79: with the loan bounded by the callee's fixed inputs the entry is prepared
/// (the W76 line prints; no refusal). The fault `no-fixed` gives the refusal back.
#[test]
fn e5c_w79_a_c_variadic_tail_binds_no_loan() {
    let env = [("CRAT_E5C_W76", "1")];
    let on = w71_lines("w79-shapes", "on", &env);
    assert!(
        on.iter().any(|l| l.starts_with("discharged ")),
        "the entry is prepared: {on:?}"
    );
    let text = w63_child(
        "w79-shapes",
        &[("CRAT_E5C_W76", "1"), ("CRAT_E5C_W79_FAULT", "no-fixed")],
    );
    assert!(
        text.contains("unresolved callee argument: mk_list argument 4 of 3"),
        "the fault must be caught: {text}"
    );
}

/// L01¹³'s arms over the W63 child's: L01¹¹'s and L01¹²'s lines, the guarded
/// repair, and the allocator contract on (R691-1).
const L01P13_ARMS: &[(&str, &str)] = &[
    ("CRAT_ERA5C_LEND", "on"),
    ("CRAT_ERA5C_REF_PEEL_ZERO", "on"),
    ("CRAT_ERA5C_RETIRE_FRESH", "on"),
    ("CRAT_ERA5C_RETIRE_ROUTE_USE", "on"),
    ("CRAT_ERA5C_TYPED_SOLE", "on"),
    ("CRAT_ERA5C_ALPHA_RETURNS", "on"),
    ("CRAT_ERA5C_REALLOC_REFUTE", "on"),
    ("CRAT_ERA5C_REALLOC_NONZERO", "on"),
    ("CRAT_ERA5C_ALLOCATOR_CONTRACT", "on"),
    ("CRAT_BO_REPAIR", "guarded"),
    ("CRAT_BO_SAFE_MONO", "per_site"),
    ("CRAT_NB4R_ROUTING", "on"),
    ("CRAT_E5C_W63_MODEL_ONLY", "1"),
];

fn l01p13_lines(shape: &str, extra: &[(&str, &str)]) -> Vec<String> {
    let mut env = L01P13_ARMS.to_vec();
    env.extend_from_slice(extra);
    w63_lines(shape, &env)
}

/// W83 (R697-6; analysis-fanout 018, era-5c 106): carrays' `void *` swap. The
/// allocator finder of `points_to` followed `_0 <- p1 <- p0 <- p1 <- ...` with no
/// visited set and overflowed the stack before the solve began; RED at L01¹²
/// (the child aborts). With the visited set the program solves.
const W83_SWAP: &str = r#"
#![allow(unused)]
pub unsafe extern "C" fn f(mut p0: *mut ::core::ffi::c_void, mut p1: *mut ::core::ffi::c_void) -> *mut ::core::ffi::c_void { p0 = p1; p1 = p0; return p1; }
"#;

#[test]
fn e5c_w83_a_void_pointer_swap_solves() {
    let lines = l01p13_lines("w83-swap", &[]);
    w63_kind(&lines, "f::_0@d0");
}

/// W84 (R697-3; analysis-fanout 020 STOP 1): the paper's linked list with the
/// fork's `pub const NULL` item. The item's body names no program function, so
/// caller coverage is complete and the list settles as it does with `0` for
/// `NULL`: `next` Owning, `push`'s formal Owning, `last` Ref. RED at L01¹²: the
/// item held coverage (`CompilerBodies`) and `next` settled Raw. The fault
/// `CRAT_E5C_W84_FAULT=no-inert` (test builds) admits no inert body.
const W84_LIST: &str = r#"
#![allow(unused_mut)]
extern "C" {
    fn malloc(__size: usize) -> *mut ::core::ffi::c_void;
    fn free(__ptr: *mut ::core::ffi::c_void);
}
#[repr(C)]
pub struct Node {
    pub val: ::core::ffi::c_int,
    pub next: *mut Node,
}
pub const NULL: *mut ::core::ffi::c_void = ::core::ptr::null_mut::<::core::ffi::c_void>();
#[no_mangle]
pub unsafe extern "C" fn push(mut head: *mut Node, mut val: ::core::ffi::c_int) -> *mut Node {
    let mut n = malloc(::core::mem::size_of::<Node>()) as *mut Node;
    (*n).val = val;
    (*n).next = head;
    return n;
}
#[no_mangle]
pub unsafe extern "C" fn last(mut head: *mut Node) -> *mut Node {
    while !(*head).next.is_null() { head = (*head).next; }
    return head;
}
#[export_name = "drop"]
pub unsafe extern "C" fn drop_0(mut head: *mut Node) {
    if head.is_null() { return; }
    drop_0((*head).next);
    free(head as *mut ::core::ffi::c_void);
}
"#;
const W84_NULL_ITEM: &str =
    "pub const NULL: *mut ::core::ffi::c_void = ::core::ptr::null_mut::<::core::ffi::c_void>();\n";

/// W84's static: a pointer-free static the points-to type shapes read after
/// coverage is collected. Reading the inert test from the static's MIR stole
/// that body first (tisp: "attempted to read from stolen value" in `ty_shape`).
const W84_STATIC: &str = r#"
pub static mut COUNT: ::core::ffi::c_int = 0;
#[no_mangle]
pub unsafe extern "C" fn count() -> ::core::ffi::c_int { COUNT += 1; return COUNT; }
"#;

#[test]
fn e5c_w84_an_inert_const_item_holds_no_caller_coverage() {
    assert!(W84_LIST.contains(W84_NULL_ITEM));
    let null = l01p13_lines("w84-null", &[]);
    let zero = l01p13_lines("w84-zero", &[]);
    for key in [
        "Node::field1@d0",
        "push::_1@d0",
        "last::_1@d0",
        "last::_0@d0",
    ] {
        assert_eq!(w63_kind(&null, key), w63_kind(&zero, key), "{key}");
    }
    assert_eq!(w63_kind(&null, "Node::field1@d0"), "owning");
    assert_eq!(w63_kind(&null, "push::_1@d0"), "owning");
    assert_eq!(w63_kind(&null, "last::_1@d0"), "ref");
    let with_static = l01p13_lines("w84-static", &[]);
    assert_eq!(w63_kind(&with_static, "Node::field1@d0"), "owning");
    let fault = l01p13_lines("w84-null", &[("CRAT_E5C_W84_FAULT", "no-inert")]);
    assert_eq!(
        w63_kind(&fault, "Node::field1@d0"),
        "raw",
        "the fault must be caught: {fault:?}"
    );
}

/// W84's corpus read (R697-3 (3)): the compiler bodies a derived program's caller
/// coverage still holds on, once the inert ones are admitted. No solve.
#[test]
#[ignore = "driven by era-5c's R697-3 corpus read"]
fn e5c_inner_w84_coverage_of_file() {
    use rustc_hir::{ItemKind, OwnerNode};
    let path = std::env::var("CRAT_E5C_W84_SOURCE").expect("CRAT_E5C_W84_SOURCE");
    let source = std::fs::read_to_string(&path).expect("source");
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let c = super::licensing::caller_coverage::Coverage::collect(&program);
        let unconfigured: Vec<_> = c
            .compiler_bodies
            .iter()
            .filter(|b| !c.configured_functions.contains(*b) && !c.derived_impl_bodies.contains(*b))
            .collect();
        let held: Vec<_> = unconfigured
            .iter()
            .filter(|b| !c.inert_bodies.contains(**b))
            .collect();
        eprintln!(
            "E5C_W84 {path} unconfigured={} inert={} held={} indirect={} values={} asm={}",
            unconfigured.len(),
            unconfigured.len() - held.len(),
            held.len(),
            c.indirect_calls.len(),
            c.function_values.len(),
            c.inline_assembly.len()
        );
        for body in held {
            eprintln!("E5C_W84 held {body}");
        }
    });
}

/// W85 (R701; analysis-fanout 023 STOP 1): G, AVL's `insert` one level down, as the
/// Yale-PROCTOR fork translates it -- `NULL` becomes `::core::ptr::null_mut::<Node>()`,
/// a library call, where the older translation (the corpus, AVL) writes `0 as *mut Node`.
/// RED at L01¹²: the call went through the opaque-call arm, which pins the new value
/// non-owning, so `new_node`'s `n->next = NULL` forbade `next`'s ownership
/// (`coherence::field-and` -> `link-own` -> `own-assume[opaque-call-arg]`) and `next`
/// settled Ref. GREEN: the null constructor is a null constant, as the cast is; `next`
/// Owning, `put` Owning in and out, `last` Ref -- equal to the cast text. The fault
/// `CRAT_E5C_W85_FAULT=opaque-null` (test builds) gives the opaque arm back.
const W85_G: &str = r#"
#![allow(unused_mut)]
extern "C" { fn malloc(__size: usize) -> *mut ::core::ffi::c_void; }
#[repr(C)]
pub struct Node { pub val: ::core::ffi::c_int, pub next: *mut Node }
#[no_mangle]
pub unsafe extern "C" fn new_node(mut val: ::core::ffi::c_int) -> *mut Node {
    let mut n = malloc(::core::mem::size_of::<Node>()) as *mut Node;
    (*n).val = val;
    (*n).next = ::core::ptr::null_mut::<Node>();
    return n;
}
#[no_mangle]
pub unsafe extern "C" fn last(mut head: *mut Node) -> *mut Node {
    while !(*head).next.is_null() { head = (*head).next; }
    return head;
}
#[no_mangle]
pub unsafe extern "C" fn put(mut node: *mut Node, mut val: ::core::ffi::c_int) -> *mut Node {
    if node.is_null() { return new_node(val); }
    (*node).val = val;
    return node;
}
#[no_mangle]
pub unsafe extern "C" fn set_next(mut node: *mut Node, mut val: ::core::ffi::c_int) {
    (*node).next = put((*node).next, val);
}
"#;

#[test]
fn e5c_w85_the_null_constructor_is_a_null_constant() {
    let call = l01p13_lines("w85-call", &[]);
    let cast = l01p13_lines("w85-cast", &[]);
    for key in [
        "Node::field1@d0",
        "put::_0@d0",
        "put::_1@d0",
        "last::_0@d0",
        "last::_1@d0",
        "new_node::_0@d0",
    ] {
        assert_eq!(w63_kind(&call, key), w63_kind(&cast, key), "{key}");
    }
    assert_eq!(w63_kind(&call, "Node::field1@d0"), "owning");
    assert_eq!(w63_kind(&call, "put::_1@d0"), "owning");
    assert_eq!(w63_kind(&call, "last::_1@d0"), "ref");
    let fault = l01p13_lines("w85-call", &[("CRAT_E5C_W85_FAULT", "opaque-null")]);
    assert_eq!(
        w63_kind(&fault, "Node::field1@d0"),
        "ref",
        "the fault must be caught: {fault:?}"
    );
}

/// W76 (R677-4; era-5c 099 STOP 1 (ii)): the entry carries the retirement
/// review's discharged rows. On W71's shapes with L01¹¹'s discharges on, the
/// in-memory packet and the prepared (streamed) entry hold the same rows; the
/// fault `CRAT_E5C_W76_FAULT=no-discharged` (test builds) empties the entry's.
#[test]
fn e5c_w76_the_entry_carries_the_discharged_rows() {
    let line = |extra: &[(&str, &str)]| {
        let mut env = vec![("CRAT_E5C_W76", "1")];
        env.extend_from_slice(extra);
        w71_lines("w71-shapes", "on", &env)
            .into_iter()
            .find(|l| l.starts_with("discharged "))
            .expect("the W76 line")
    };
    let on = line(&[]);
    let portable: usize = on
        .split_whitespace()
        .find_map(|w| w.strip_prefix("portable="))
        .and_then(|n| n.parse().ok())
        .expect("portable count");
    assert!(portable >= 4, "{on}");
    assert!(on.ends_with("equal=true"), "{on}");
    let fault = line(&[("CRAT_E5C_W76_FAULT", "no-discharged")]);
    assert!(
        fault.contains(" entry=0 ") && fault.ends_with("equal=false"),
        "{fault}"
    );
}

/// W77 (R677-4): RQ5's three switches in L01¹², default-inert. On the snapshot
/// fixture (`two(p, p)`): by default precise replay plans a C-9 mark and the
/// identity reads `a5_mode=precise_replay`, `mutability=foster-from-program-v1`,
/// `era5c_a5_snapshot=true`; `CRAT_ERA5C_A5_SNAPSHOT=off` plans none;
/// `CRAT_BO_A5_MODE=baseline` turns A5 off; `CRAT_BO_MUT_FACTS=off` names all-mut.
#[test]
fn e5c_w77_the_rq5_switches() {
    let run = |env: &[(&str, &str)]| -> Vec<String> {
        child(
            "analyses::borrow_ownership::a5_producer::tests::e5c_inner_w77",
            env,
        )
        .lines()
        .filter_map(|l| l.find("E5C_W77 ").map(|i| l[i + 8..].to_owned()))
        .collect()
    };
    let marks = |lines: &[String]| -> usize {
        lines
            .iter()
            .find_map(|l| l.split("marks=").nth(1))
            .and_then(|n| n.parse().ok())
            .expect("marks")
    };
    let default = run(&[]);
    assert!(marks(&default) > 0, "{default:?}");
    for line in [
        "a5_mode=precise_replay",
        "mutability=foster-from-program-v1",
        "era5c_a5_snapshot=true",
    ] {
        assert!(default.iter().any(|l| l == line), "{line}: {default:?}");
    }
    let snapshot = run(&[("CRAT_ERA5C_A5_SNAPSHOT", "off")]);
    assert_eq!(marks(&snapshot), 0, "{snapshot:?}");
    assert!(
        snapshot.iter().any(|l| l == "era5c_a5_snapshot=false"),
        "{snapshot:?}"
    );
    let overlap = run(&[("CRAT_BO_A5_MODE", "baseline")]);
    assert_eq!(marks(&overlap), 0, "{overlap:?}");
    assert!(
        overlap.iter().any(|l| l == "a5_mode=baseline"),
        "{overlap:?}"
    );
    let mutable = run(&[("CRAT_BO_MUT_FACTS", "off")]);
    assert!(
        mutable.iter().any(|l| l == "mutability=all-mut-v1"),
        "{mutable:?}"
    );
}
