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
    for (name, code) in [
        ("H65", W49_H65),
        ("OWNER", W49_OWNER),
        ("TABLE", W43_TULIP),
    ] {
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
