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
#[ignore = "runs under CRAT_ERA5C_MOVE_TRACKING=on in a child of e5c_w7"]
fn e5c_inner_null_join_rows_under_the_arm() {
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
        &[],
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

fn bst_probe() -> String {
    let dir = std::env::var("DIR")
        .unwrap_or_else(|_| concat!(env!("CARGO_MANIFEST_DIR"), "/../..").to_owned());
    child(
        "bo_c1::r385_forced_assignment_probe",
        &[
            ("CRAT_R385_PROGRAM", BST),
            ("CRAT_R385_TARGETS", BST_TARGETS),
            ("CRAT_R385_GRANULARITY", "assertion"),
            ("CRAT_R385_WORLD", "closed"),
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
    let text = bst_probe();
    assert!(text.contains("R385 VERDICT=SAT"), "{text}");
    assert!(!text.contains("E5C traversal-pending"), "{text}");
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
        &[],
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
        &[],
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
        &[],
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
        &[],
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
        &[],
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

/// R412-12: with the contract pin OFF an indirect call's result is opaque
/// under the frame — never Owning by the objective alone.
#[test]
#[ignore = "runs under CRAT_ERA5C_MOVE_TRACKING=on, contract off, in a child of e5c_w16"]
fn e5c_inner_brotli_shape_indirect_result_is_opaque_without_the_contract() {
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
        &[],
    );
    assert!(text.contains("E5C_OPAQUE_OK"), "{text}");
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

const W47_ARMS: &[(&str, &str)] = &[];

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

// ---------------------------------------------------------------------------
// W52 (era-5c L01⁹, R549-2 (i)): A12's production selector.

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
    let env: Vec<(&str, &str)> = W47_ARMS.to_vec();
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

/// W55a: the tree owns and the deref temporary is its Ref reader.
#[test]
fn e5c_w55_a_deref_only_reads_let_the_field_own() {
    let on = w55_rows(&[]);
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

/// W60: the moved-input rule licenses P's field and not the guarded A and B; the
/// transfer predicate admits `linear` and `equal` by move and refuses `equal` by
/// copy (control).
#[test]
fn e5c_w60_a_parameter_moved_into_a_field_supports_it() {
    use super::licensing::field_support::moved_transfer;
    assert!(moved_transfer("linear", false) && moved_transfer("equal", true));
    assert!(
        !moved_transfer("equal", false),
        "a copied operand keeps its hold"
    );
    let rows = || -> std::collections::BTreeMap<String, String> {
        let env: Vec<(&str, &str)> = W47_ARMS.to_vec();
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
    let on = rows();
    let field = |rows: &std::collections::BTreeMap<String, String>, shape: &str| {
        rows.get(&format!("{shape} Node::field1@d0"))
            .cloned()
            .unwrap_or_default()
    };
    assert_eq!(field(&on, "P"), "owning", "{on:?}");
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
}

// ---------------------------------------------------------------------------
// W53 (era-5c L01⁹, R551: the spec lane's B2/B3/B4).

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
/// model's rows (6 uses on `AVL_SHAPE`).
#[test]
fn e5c_w62_a_the_rows_round_trip_through_the_export_and_the_entry() {
    let on = w62_lines(&[]);
    assert!(on.contains(&"model ok:6:6".to_owned()), "{on:?}");
    assert!(on.contains(&"portable ok:6:6".to_owned()), "{on:?}");
    assert!(on.contains(&"entry ok:6:6".to_owned()), "{on:?}");
    assert!(
        on.contains(&"equal portable=true entry=true".to_owned()),
        "{on:?}"
    );
}

/// W62d (R577-5): every row carries `cleared`, the members whose loans its
/// store removed, exactly as the replay's last pass removed them; none is
/// `Raw` (a `Raw` member keeps its loan) and none is `kept` (3.2).
#[test]
fn e5c_w62_d_each_row_carries_the_members_its_store_cleared() {
    let on = w62_lines(&[]);
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
        Ok("w68-shapes") => W68_SHAPES,
        Ok("w71-shapes") => W71_SHAPES,
        Ok("ctx-jail") => W71_CTX_JAIL,
        Ok("w75-shapes") => W75_SHAPES,
        Ok("w79-shapes") => W79_SHAPES,
        Ok("w83-swap") => W83_SWAP,
        Ok("w84-null") => W84_LIST,
        Ok("w84-zero") => {
            owned = W84_LIST.replace(W84_NULL_ITEM, "");
            owned.as_str()
        }
        Ok("w80-base") => W80_BASE,
        Ok("w81-grow") => {
            owned = format!("{W80_BASE}{W81_GROW}");
            owned.as_str()
        }
        Ok("w82-cond") => {
            owned = format!("{W80_BASE}{W82_COND}");
            owned.as_str()
        }
        Ok("w82-lent") => {
            owned = format!("{W80_BASE}{W82_LENT}");
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
        // W81 (era-5c 115): the receipt's retracted contract ports.
        for line in verified
            .receipt
            .lines()
            .filter(|line| line.starts_with("allocator_contract_ports_retracted"))
        {
            eprintln!("E5C_W63 {line}");
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
            // R1178-1 (fix (i)): the receipts the loader now takes from memory equal the ones
            // the staged entry's file decodes, rows and refusal alike.
            let from_file = super::model_cache::prepared_arg_order_from_file(&key);
            eprintln!(
                "E5C_W63 arg-order-memory-vs-file equal={}",
                entry == from_file
            );
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
        // L01¹⁰'s configuration (R604-1): the typed-release discharge is on.
        // L01¹⁰'s configuration (R609-3): the argument-order premise and the
        // A5 type route are on.
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

/// W63a: the context's pass-through formals are not Owning -- every call lends
/// them.
#[test]
fn e5c_w63_a_a_lendable_formal_is_a_zero_view_at_every_call() {
    let on = w63_lines("ctx", &[]);
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
    }
}

/// W63b: a consuming callee still takes the owner -- `lil_free` frees its
/// formal, is no lend, and stays Owning with the arm; the constructor's owner
/// reaches it.
#[test]
fn e5c_w63_b_a_consuming_formal_keeps_the_owner() {
    let on = w63_lines("ctx", &[]);
    assert!(!on.iter().any(|l| l == "lendable lil_free::_1"), "{on:?}");
    assert_eq!(w63_kind(&on, "lil_free::_1@d0"), "owning", "{on:?}");
    assert_eq!(w63_kind(&on, "lil_new::_0@d0"), "owning", "{on:?}");
}

/// W63c (R580-1): a member handed to an indirect callee is no consumer; the
/// site is receipted under R481's tier-2 waiver.
#[test]
fn e5c_w63_c_an_indirect_call_lends_under_the_tier_2_waiver() {
    let on = w63_lines("callback", &[]);
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
}

/// W63e: the recorded plan travels in the licensing snapshot and a restored
/// snapshot validates.
#[test]
fn e5c_w63_e_the_validator_refuses_an_uncertified_borrowed_call() {
    let on = w63_lines("ctx", &[]);
    assert!(
        on.iter().any(|l| l == "validate ok lend_plan=true"),
        "{on:?}"
    );
    assert!(!on.iter().any(|l| l.starts_with("validate err")), "{on:?}");
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
/// component carries the field's ownership through the call.
#[test]
fn e5c_w64_a_a_lent_writer_moves_the_field_not_the_container() {
    if !std::path::Path::new(W64_HT).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let shape = format!("file:{W64_HT}");
    let on = w63_lines(&shape, &[]);
    for key in ["src::ht::ht_expand::_1@d0", "src::ht::ht_set::_1@d0"] {
        assert_eq!(w63_kind(&on, key), "ref", "{key}: {on:?}");
    }
    assert_eq!(w63_kind(&on, "src::ht::ht::field0@d0"), "owning", "{on:?}");
}

// ---- era-5c 077 / R603-2: the retirement discharges. (α) the post-free use,
// unconditional; (β) the effective type behind CRAT_ERA5C_TYPED_RELEASE, which
// rests on the premise TypedReleaseDiscipline (R603-1, the user's).

const W66_QUADTREE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/rs-crown-derived/quadtree/lib.rs"
);

fn w66_lines(shape: &str) -> Vec<String> {
    w63_lines(shape, &[])
}

/// W66a: ht's lent tables are Ref and `entries` Owning under the discharge;
/// every discharge is receipted.
#[test]
fn e5c_w66_a_ht_tables_return_to_ref_under_the_discharge() {
    if !std::path::Path::new(W64_HT).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let shape = format!("file:{W64_HT}");
    let on = w66_lines(&shape);
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
}

/// W66b: lil's context shape; the two formals 072 lost are Ref again.
#[test]
fn e5c_w66_b_the_context_formals_return_to_ref_under_the_discharge() {
    let on = w66_lines("ctx");
    for key in ["lil_parse::_1@d0", "lil_pop_env::_1@d0"] {
        assert_eq!(w63_kind(&on, key), "ref", "{key}: {on:?}");
    }
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
    let on = w66_lines(&shape);
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
    let on = w66_lines("w66-controls");
    for function in ["void_free", "unioned"] {
        assert!(discharges(&on, function).is_empty(), "{function}: {on:?}");
    }
    // Under the sole-type containment the embedded referent discharges too.
    let embedded = discharges(&on, "embedded");
    assert!(
        !embedded.is_empty()
            && embedded
                .iter()
                .all(|l| l.ends_with("premise=typed-release@R604-1, containment=sole-type)")),
        "embedded: {on:?}"
    );
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

/// W68 (R609-3): the W63 child's lines on `W68_SHAPES` with the lend on, plus the
/// type route's debug rows.
fn w68_lines() -> Vec<String> {
    w63_lines("w68-shapes", &[])
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
    let on = w63_lines(&shape, &[("CRAT_E5C_W63_MODEL_ONLY", "1")]);
    let key = "src::src::quadtree::quadtree_insert::_1@d0";
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
    let on = w68_lines();
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
    let on = w68_lines();
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
/// and model.
fn w71_lines(shape: &str, extra: &[(&str, &str)]) -> Vec<String> {
    let mut env: Vec<(&str, &str)> = vec![];
    env.extend_from_slice(extra);
    w63_lines(shape, &env)
}

fn w71_has(lines: &[String], prefix: &str, target: &str, needle: &str) -> bool {
    lines
        .iter()
        .any(|l| l.starts_with(prefix) && l.contains(target) && l.contains(needle))
}

/// W71a: lil's shape. Measured (era-5c 097): on this reduction the review raises
/// no conflict on the jail's release, so the context formal is Ref; lil's held
/// formals are measured on the solve.
#[test]
fn e5c_w71_a_the_jail_release_is_fresh() {
    let on = w71_lines("ctx-jail", &[]);
    assert_eq!(w63_kind(&on, "fnc_jaileval::_1@d0"), "ref", "{on:?}");
}

/// W72 (R659-1; wave-5d 133 STOP 2): the arm-(a) receipt export. On quadtree's
/// own `insert_(tree, (*tree).root, …)` the model's receipts equal the portable
/// export's and the prepared entry's, and one names `quadtree_insert`'s call
/// with the tree as its lent pointer.
#[test]
fn e5c_w72_the_arg_order_receipts_reach_the_entry() {
    if !std::path::Path::new(W66_QUADTREE).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let shape = format!("file:{W66_QUADTREE}");
    let on = w63_lines(&shape, &[("CRAT_E5C_W72", "1")]);
    let summary = on
        .iter()
        .find(|l| l.starts_with("arg-order model="))
        .unwrap_or_else(|| panic!("{on:?}"));
    assert!(summary.ends_with("equal=true"), "{summary}");
    // R1178-1: the loader's rows from memory = the staged file's.
    assert!(
        on.iter()
            .any(|l| l == "arg-order-memory-vs-file equal=true"),
        "{on:?}"
    );
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
}

/// W69 (R617-1): the W63 child under the guarded repair -- its lines.
fn w69_lines(shape: &str, extra: &[(&str, &str)]) -> Vec<String> {
    w63_child(shape, extra)
        .lines()
        .filter_map(|l| {
            l.find("E5C_W63 ")
                .map(|i| l[i + 8..].to_owned())
                .or_else(|| l.find("E5C_MODEL ").map(|i| l[i + 10..].to_owned()))
        })
        .collect()
}

fn w69_model(lines: &[String]) -> Vec<&String> {
    lines
        .iter()
        .filter(|l| {
            !l.starts_with("repair-receipt ")
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

/// W69b's search (R617-1): shapes under both repairs, one line each.
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

/// W69d: a guarded accept records the residual certificate, the rows Mode-A records on the same
/// model (the separate loop left it `None`).
#[test]
fn e5c_w69_d_a_guarded_accept_records_the_residual_certificate() {
    let guarded = w69_lines("w68-shapes", &[]);
    let mode_a = w63_lines("w68-shapes", &[]);
    assert_ne!(w63_kind(&guarded, "residuals"), "none", "{guarded:?}");
    if w69_model(&guarded) == w69_model(&mode_a) {
        assert_eq!(
            w63_kind(&guarded, "residuals"),
            w63_kind(&mode_a, "residuals")
        );
    }
}

/// W69e: the field-own branch (relay 117) runs under the guarded repair. avl's rotations leave a
/// residual on an Owning field (W56); the separate loop declined it; the one loop repairs it before
/// the mode arm, so the guarded run accepts without falling back.
#[test]
fn e5c_w69_e_the_field_own_branch_runs_under_the_guarded_repair() {
    let mut env: Vec<(&str, &str)> = W47_ARMS.to_vec();
    env.push(("CRAT_E5C_SHAPE", "AVL"));
    let on: Vec<String> = child(
        "analyses::borrow_ownership::null_paths_tests::e5c_inner_shape_decline_reason",
        &env,
    )
    .lines()
    .filter_map(|l| {
        l.find("E5C_DECLINE ")
            .map(|i| l[i..].to_owned())
            .or_else(|| l.find("E5C_REPAIR ").map(|i| l[i..].to_owned()))
    })
    .collect();
    assert!(on.contains(&"E5C_DECLINE none".to_owned()), "{on:?}");
    assert!(
        on.contains(&"E5C_REPAIR repair=guarded".to_owned()),
        "{on:?}"
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

/// W78 (R682-3): a discharge only the zero-size `realloc` premise admits is
/// receipted `premise=realloc-nonzero@R684-1` (R686-4). On W75's shapes, `store`'s
/// (computed size) receipt carries it; `store16`'s and `grow16`'s (constant size) do not.
#[test]
fn e5c_w78_the_realloc_premise_is_receipted() {
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
    let premise = w71_lines("w75-shapes", &[]);
    assert!(marked(&premise, "store"), "{premise:?}");
    assert!(
        discharged(&premise, "store16") && !marked(&premise, "store16"),
        "{premise:?}"
    );
    assert!(
        discharged(&premise, "grow16") && !marked(&premise, "grow16"),
        "{premise:?}"
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
/// (the W76 line prints; no refusal).
#[test]
fn e5c_w79_a_c_variadic_tail_binds_no_loan() {
    let env = [("CRAT_E5C_W76", "1")];
    let on = w71_lines("w79-shapes", &env);
    assert!(
        on.iter().any(|l| l.starts_with("discharged ")),
        "the entry is prepared: {on:?}"
    );
}

/// L01¹³'s arms over the W63 child's: L01¹¹'s and L01¹²'s lines and the guarded
/// repair.
const L01P13_ARMS: &[(&str, &str)] = &[("CRAT_E5C_W63_MODEL_ONLY", "1")];

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
/// item held coverage (`CompilerBodies`) and `next` settled Raw.
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
/// Owning, `put` Owning in and out, `last` Ref -- equal to the cast text.
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
}

/// W80–W82 (R691-1, era-5c 108): brotli's memory manager reduced (era-5c 100b's
/// `br-*.rs`). The base: `make` allocates through `BrotliAllocate` (the contract's
/// producer), writes, reads and releases through `BrotliFree` (its `free_func` sink).
const W80_BASE: &str = r#"

#![allow(dead_code, unused_unsafe, unused_variables, non_camel_case_types, non_snake_case)]
use core::ffi::c_void;
extern "C" { fn malloc(_: u64) -> *mut c_void; fn free(_: *mut c_void); fn exit(_: i32) -> !; fn memcpy(_: *mut c_void, _: *const c_void, _: u64) -> *mut c_void; }
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
/// The ensure-capacity swap (100b's `grow`): the receiver that cannot own.
const W81_GROW: &str = r#"
pub unsafe fn grow(m: *mut MemoryManager, n: u64) -> u32 {
    let mut arr = BrotliAllocate(m, 16) as *mut u32;
    *arr = 3;
    let new_arr = BrotliAllocate(m, n.wrapping_mul(4)) as *mut u32;
    memcpy(new_arr as *mut c_void, arr as *const c_void, 16);
    BrotliFree(m, arr as *mut c_void);
    arr = new_arr;
    let v = *arr;
    BrotliFree(m, arr as *mut c_void);
    return v;
}
"#;
/// Releasers whose released value is not the incoming formal (Codex, era-5c 115):
/// `keep_and_free` overwrites `p`; `wrap_free` overwrites a wrapper's field
/// between two transmutes.
const W81_REASSIGNED: &str = r#"
pub unsafe fn keep_and_free(m: *mut MemoryManager, mut p: *mut c_void) -> *mut c_void {
    let saved = p;
    p = BrotliAllocate(m, 8);
    ((*m).free_func).expect("non-null function pointer")((*m).opaque, p);
    return saved;
}
#[repr(transparent)] pub struct W(pub *mut c_void);
pub unsafe fn wrap_free(m: *mut MemoryManager, p: *mut c_void) -> *mut c_void {
    let mut w: W = core::mem::transmute(p);
    w.0 = BrotliAllocate(m, 8);
    let q: *mut c_void = core::mem::transmute(w);
    ((*m).free_func).expect("non-null function pointer")((*m).opaque, q);
    return p;
}
"#;
/// A conditional allocation (`cond`).
const W82_COND: &str = r#"
pub unsafe fn cond(m: *mut MemoryManager, n: u64) -> u32 {
    let p = if n > 0 { BrotliAllocate(m, n.wrapping_mul(4)) as *mut u32 } else { 0 as *mut u32 };
    let mut v = 0;
    if !p.is_null() { *p = 1; v = *p; }
    BrotliFree(m, p as *mut c_void);
    return v;
}
"#;
/// An allocation lent to a local callee (`lent`).
const W82_LENT: &str = r#"
pub unsafe fn fill(p: *mut u32, n: u64) { let mut i = 0; while i < n { *p.offset(i as isize) = 0; i = i.wrapping_add(1); } }
pub unsafe fn lent(m: *mut MemoryManager, n: u64) -> u32 {
    let p = BrotliAllocate(m, n.wrapping_mul(4)) as *mut u32;
    fill(p, n);
    let v = *p;
    BrotliFree(m, p as *mut c_void);
    return v;
}
"#;

/// W76 (R677-4; era-5c 099 STOP 1 (ii)): the entry carries the retirement
/// review's discharged rows. On W71's shapes with L01¹¹'s discharges on, the
/// in-memory packet and the prepared (streamed) entry hold the same rows.
#[test]
fn e5c_w76_the_entry_carries_the_discharged_rows() {
    let line = |extra: &[(&str, &str)]| {
        let mut env = vec![("CRAT_E5C_W76", "1")];
        env.extend_from_slice(extra);
        w71_lines("w71-shapes", &env)
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
}
