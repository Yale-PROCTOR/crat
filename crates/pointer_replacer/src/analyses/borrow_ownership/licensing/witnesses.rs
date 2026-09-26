//! OL01–OL12 kind witnesses. The embedded programs are compiler inputs only.
//! Occurrence, responsibility and endpoint assertions are added at their due
//! export/transport phases; lifetime-wide owning kinds do not count live tokens.

use super::{
    super::SlotKind,
    tests::{Fixture, inspect},
};

fn assert_kinds(fixture: &Fixture, expected: &[(&str, SlotKind)]) {
    assert!(fixture.accepted, "the witness requires an accepted model");
    for &(key, kind) in expected {
        fixture.assert_kind(key, kind);
    }
}

pub(super) const BST: &str = r#"
#![allow(non_snake_case, non_camel_case_types)]
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
    fn printf(format: *const core::ffi::c_char, ...) -> i32;
}
pub struct node {
    key: i32,
    left: *mut node,
    right: *mut node,
}
pub unsafe fn newNode(key: i32) -> *mut node {
    let temp = malloc(core::mem::size_of::<node>()) as *mut node;
    (*temp).key = key;
    (*temp).left = 0 as *mut node;
    (*temp).right = 0 as *mut node;
    temp
}
pub unsafe fn insert(node: *mut node, key: i32) -> *mut node {
    if node.is_null() {
        return newNode(key);
    }
    if key < (*node).key {
        (*node).left = insert((*node).left, key);
    } else if key > (*node).key {
        (*node).right = insert((*node).right, key);
    }
    node
}
pub unsafe fn minValueNode(mut node: *mut node) -> *mut node {
    while !(*node).left.is_null() {
        node = (*node).left;
    }
    node
}
pub unsafe fn deleteNode(mut root: *mut node, key: i32) -> *mut node {
    if root.is_null() {
        return root;
    }
    if key < (*root).key {
        (*root).left = deleteNode((*root).left, key);
    } else if key > (*root).key {
        (*root).right = deleteNode((*root).right, key);
    } else {
        if (*root).left.is_null() {
            let temp = (*root).right;
            free(root as *mut core::ffi::c_void);
            return temp;
        } else if (*root).right.is_null() {
            let temp_0 = (*root).left;
            free(root as *mut core::ffi::c_void);
            return temp_0;
        }
        let temp_1 = minValueNode((*root).right);
        (*root).key = (*temp_1).key;
        (*root).right = deleteNode((*root).right, (*temp_1).key);
    }
    root
}
pub unsafe fn inorder(root: *mut node) {
    if !root.is_null() {
        inorder((*root).left);
        printf(b"%d \0".as_ptr() as *const core::ffi::c_char, (*root).key);
        inorder((*root).right);
    }
}
pub unsafe fn f() -> *mut node {
    let mut root = insert(0 as *mut node, 2);
    root = insert(root, 1);
    root = insert(root, 3);
    inorder(root);
    deleteNode(root, 2)
}
"#;

/// R336-5: bst's `deleteNode` uses BOTH of its structure's pointer fields, so
/// the member family has to admit both. Before the iteration it admitted one
/// and held on the second, which could not express this shape at all. Gating,
/// unlike the preflight census, because a killer needs something to kill.
#[test]
fn r336_5_bst_delete_node_admits_both_of_its_fields() {
    super::graph_tests::with_facts(BST, |facts| {
        let members = super::fold_eligibility::member_plan(facts).unwrap_or_default();
        let widest = members
            .iter()
            .map(|decision| decision.fields.len())
            .max()
            .unwrap_or_default();
        assert_eq!(
            widest,
            2,
            "deleteNode uses two fields and the member family must admit both: {:?}",
            members
                .iter()
                .map(|decision| (
                    decision.declaration.call.caller.clone(),
                    decision.fields.clone()
                ))
                .collect::<Vec<_>>()
        );
    });
}

#[test]
fn c08_bst_attested_chain_obligations() {
    let fixture = super::tests::inspect_era5_frame(BST);
    eprintln!(
        "C08_BST_FRAME={}",
        serde_json::json!({
            "accepted":fixture.accepted,"kinds":fixture.kinds.iter().map(|(k,v)| (k.clone(),format!("{v:?}"))).collect::<std::collections::BTreeMap<_,_>>(),"error":fixture.construction_error,"commits":fixture.commit_trace,
            "snapshots":fixture.export.ownership_licensing.as_ref().map(|rows| rows.iter().map(|s| serde_json::json!({
                "offset":s.offset,"field_support":s.field_support,"recursive":s.recursive,
                "traversal_correspondences":s.traversal_correspondences,"reader_transfers":s.reader_transfers,
                "grant_holds":s.grant_holds,
                "boundaries":s.metadata.boundaries,
            })).collect::<Vec<_>>()),
        })
    );
    assert_kinds(
        &fixture,
        &[
            ("node.left", SlotKind::Owning),
            ("node.right", SlotKind::Owning),
            ("minValueNode::node", SlotKind::Ref),
            ("deleteNode::temp_1", SlotKind::Ref),
        ],
    );
}

#[test]
fn ol01_bst_return_field_and_free_chain_owns_the_named_carriers() {
    let fixture = inspect(BST);
    assert_kinds(
        &fixture,
        &[
            ("node.left", SlotKind::Owning),
            ("node.right", SlotKind::Owning),
            ("newNode::temp", SlotKind::Owning),
            ("newNode::_0", SlotKind::Owning),
            ("insert::node", SlotKind::Owning),
            ("insert::_0", SlotKind::Owning),
            ("deleteNode::root", SlotKind::Owning),
            ("deleteNode::temp", SlotKind::Owning),
            ("deleteNode::temp_0", SlotKind::Owning),
        ],
    );
}

#[test]
fn ol02_bst_field_readers_keep_references_beside_the_owning_delete_path() {
    let fixture = inspect(BST);
    assert_kinds(
        &fixture,
        &[
            ("minValueNode::node", SlotKind::Ref),
            ("minValueNode::_0", SlotKind::Ref),
            ("deleteNode::temp_1", SlotKind::Ref),
            ("inorder::root", SlotKind::Ref),
            ("deleteNode::root", SlotKind::Owning),
            ("node.left", SlotKind::Owning),
            ("node.right", SlotKind::Owning),
        ],
    );
}

#[test]
fn ol03_avl_single_and_double_rotations_transport_source_only_owners() {
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct Avl { key: i32, left: *mut Avl, right: *mut Avl }
pub unsafe fn make(key: i32) -> *mut Avl {
    let node = malloc(core::mem::size_of::<Avl>()) as *mut Avl;
    (*node).key = key;
    (*node).left = 0 as *mut Avl;
    (*node).right = 0 as *mut Avl;
    node
}
pub unsafe fn rotate_right(y: *mut Avl) -> *mut Avl {
    let x = (*y).left;
    let subtree = (*x).right;
    (*x).right = y;
    (*y).left = subtree;
    x
}
pub unsafe fn rotate_left(x: *mut Avl) -> *mut Avl {
    let y = (*x).right;
    let subtree = (*y).left;
    (*y).left = x;
    (*x).right = subtree;
    y
}
pub unsafe fn rotate_left_right(root: *mut Avl) -> *mut Avl {
    (*root).left = rotate_left((*root).left);
    rotate_right(root)
}
pub unsafe fn rotate_right_left(root: *mut Avl) -> *mut Avl {
    (*root).right = rotate_right((*root).right);
    rotate_left(root)
}
pub unsafe fn f(left: bool) -> *mut Avl {
    let root = make(2);
    if left {
        (*root).left = make(0);
        (*(*root).left).right = make(1);
        rotate_left_right(root)
    } else {
        (*root).right = make(4);
        (*(*root).right).left = make(3);
        rotate_right_left(root)
    }
}
"#,
    );
    assert_kinds(
        &fixture,
        &[
            ("Avl.left", SlotKind::Owning),
            ("Avl.right", SlotKind::Owning),
            ("make::node", SlotKind::Owning),
            ("make::_0", SlotKind::Owning),
            ("rotate_right::y", SlotKind::Owning),
            ("rotate_right::x", SlotKind::Owning),
            ("rotate_right::subtree", SlotKind::Owning),
            ("rotate_left::x", SlotKind::Owning),
            ("rotate_left::y", SlotKind::Owning),
            ("rotate_left::subtree", SlotKind::Owning),
            ("rotate_left_right::root", SlotKind::Owning),
            ("rotate_right_left::root", SlotKind::Owning),
            ("f::_0", SlotKind::Owning),
        ],
    );
}

const RETURN_CHAIN: &str = r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn make() -> *mut i32 {
    let value = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *value = 7;
    value
}
pub unsafe fn wrapper() -> *mut i32 { make() }
pub unsafe fn consume(value: *mut i32) {
    free(value as *mut core::ffi::c_void);
}
pub unsafe fn receiver() -> i32 {
    let value = wrapper();
    let result = *value;
    consume(value);
    result
}
"#;

#[test]
fn ol04_return_only_wrappers_transport_ownership_to_receiver_and_consumer() {
    let fixture = inspect(RETURN_CHAIN);
    assert_kinds(
        &fixture,
        &[
            ("make::value", SlotKind::Owning),
            ("make::_0", SlotKind::Owning),
            ("wrapper::_0", SlotKind::Owning),
            ("receiver::value", SlotKind::Owning),
            ("consume::value", SlotKind::Owning),
        ],
    );
}

#[test]
fn ol05_source_only_return_is_an_owning_exit_without_a_free() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(size: usize) -> *mut core::ffi::c_void; }
pub unsafe fn make() -> *mut i32 {
    let value = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *value = 1;
    value
}
pub unsafe fn wrapper() -> *mut i32 { make() }
"#,
    );
    assert_kinds(
        &fixture,
        &[
            ("make::value", SlotKind::Owning),
            ("make::_0", SlotKind::Owning),
            ("wrapper::_0", SlotKind::Owning),
        ],
    );
}

#[test]
fn ol05_source_free_recursive_scc_does_not_create_an_owner() {
    let fixture = inspect(
        r#"
pub unsafe fn first(p: *mut i32, n: u32) -> *mut i32 {
    if n == 0 { p } else { second(p, n - 1) }
}
pub unsafe fn second(p: *mut i32, n: u32) -> *mut i32 {
    if n == 0 { p } else { first(p, n - 1) }
}
"#,
    );
    assert!(fixture.accepted);
    for key in ["first::p", "first::_0", "second::p", "second::_0"] {
        fixture.assert_not_owning(key);
    }
}

#[test]
fn ol06_field_only_put_take_and_release_transport_one_payload() {
    // Era-5a's explicit closed frame is required for original-cell caller
    // coverage; the unattested negative remains in chain_permission tests.
    let fixture = super::tests::inspect_era5_frame(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct Cell { ptr: *mut i32 }
pub unsafe fn make() -> *mut i32 {
    let value = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *value = 5;
    value
}
pub unsafe fn put(cell: *mut Cell, value: *mut i32) { (*cell).ptr = value; }
pub unsafe fn take(cell: *mut Cell) -> *mut i32 {
    let value = (*cell).ptr;
    (*cell).ptr = 0 as *mut i32;
    value
}
pub unsafe fn release(cell: *mut Cell) {
    let value = take(cell);
    free(value as *mut core::ffi::c_void);
}
pub unsafe fn f() {
    let owner = make();
    let mut cell = Cell { ptr: 0 as *mut i32 };
    put(&mut cell, owner);
    release(&mut cell);
}
"#,
    );
    assert_kinds(
        &fixture,
        &[
            ("Cell.ptr", SlotKind::Owning),
            ("f::owner", SlotKind::Owning),
            ("put::value", SlotKind::Owning),
            ("take::value", SlotKind::Owning),
            ("take::_0", SlotKind::Owning),
            ("release::value", SlotKind::Owning),
            ("put::cell", SlotKind::Ref),
            ("take::cell", SlotKind::Ref),
            ("release::cell", SlotKind::Ref),
        ],
    );
}

#[test]
fn ol06_same_field_in_distinct_objects_does_not_own_the_stack_payload() {
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct Cell { ptr: *mut i32 }
pub unsafe fn put(cell: *mut Cell, value: *mut i32) { (*cell).ptr = value; }
pub unsafe fn take(cell: *mut Cell) -> *mut i32 {
    let value = (*cell).ptr;
    (*cell).ptr = 0 as *mut i32;
    value
}
pub unsafe fn f() -> i32 {
    let owner = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *owner = 5;
    let mut stack = 9;
    let mut first = Cell { ptr: 0 as *mut i32 };
    let mut second = Cell { ptr: 0 as *mut i32 };
    put(&mut first, owner);
    put(&mut second, &mut stack);
    let borrowed = take(&mut second);
    let result = *borrowed;
    let allocated = take(&mut first);
    free(allocated as *mut core::ffi::c_void);
    result
}
"#,
    );
    assert!(fixture.accepted);
    for key in ["Cell.ptr", "take::_0", "f::borrowed"] {
        fixture.assert_not_owning(key);
    }
}

#[test]
fn ol07_ifl3_owns_aggregate_payload_and_keeps_struct_reference_nonowning() {
    // Literal IFL3 sequence: aggregate, read, callee free, return saved scalar.
    // Use the accepted era-5 frame's explicit frozen-graph attestation. The
    // unattested public-entry case remains a separate conservative control.
    let fixture = super::tests::inspect_era5_frame(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct H { ptr: *mut i32 }
pub unsafe fn release(h: *mut H) { free((*h).ptr as *mut core::ffi::c_void); }
pub unsafe fn f() -> i32 {
    let owner = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *owner = 1;
    let mut h = H { ptr: owner };
    let before = *h.ptr;
    release(&mut h);
    before
}
"#,
    );
    if fixture.kinds.get("H.ptr") != Some(&SlotKind::Owning) {
        eprintln!("C05_IFL3_MODEL_EVIDENCE={}", fixture.origin_json);
        eprintln!("C05_IFL3_REPAIR_TRACE={:?}", fixture.commit_trace);
        eprintln!("C05_IFL3_RETIREMENT={:?}", fixture.export.retirement_rounds);
    }
    assert_kinds(
        &fixture,
        &[
            ("f::owner", SlotKind::Owning),
            ("H.ptr", SlotKind::Owning),
            ("release::h", SlotKind::Ref),
        ],
    );
}

#[test]
fn ol08_stack_field_and_outer_struct_reference_are_not_ownership_sources() {
    let fixture = inspect(
        r#"
pub struct H { ptr: *mut i32 }
pub unsafe fn read(h: *mut H) -> i32 { *(*h).ptr }
pub unsafe fn f() -> i32 {
    let mut stack = 1;
    let mut h = H { ptr: &mut stack };
    read(&mut h)
}
"#,
    );
    assert!(fixture.accepted);
    fixture.assert_not_owning("H.ptr");
    fixture.assert_kind("read::h", SlotKind::Ref);
}

#[test]
fn ol08_shared_struct_reference_does_not_license_taking_its_payload() {
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct H { ptr: *mut i32 }
pub unsafe fn take_shared(h: &H) { free(h.ptr as *mut core::ffi::c_void); }
pub unsafe fn f() {
    let owner = malloc(core::mem::size_of::<i32>()) as *mut i32;
    let h = H { ptr: owner };
    take_shared(&h);
}
"#,
    );
    if fixture.accepted {
        fixture.assert_not_owning("H.ptr");
        fixture.assert_not_owning("take_shared::h");
    }
}

#[test]
fn ol08_payload_retirement_cannot_hide_another_full_call_reference() {
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct H { ptr: *mut i32 }
pub unsafe fn release(h: *mut H, protected: *const i32) -> i32 {
    let before = *protected;
    free((*h).ptr as *mut core::ffi::c_void);
    before
}
pub unsafe fn f() -> i32 {
    let owner = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *owner = 1;
    let mut h = H { ptr: owner };
    release(&mut h, owner)
}
"#,
    );
    // The raw input reads before free. A selected Ref parameter would instead
    // protect that payload until return, although its last source read is past.
    if fixture.accepted {
        fixture.assert_kind("release::protected", SlotKind::Raw);
        fixture.assert_not_owning("release::h");
    }
}

#[test]
fn ol09_linear_copy_partner_free_preserves_both_lifetime_kind_links() {
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn f() {
    let p = malloc(core::mem::size_of::<i32>()) as *mut i32;
    let q = p;
    free(q as *mut core::ffi::c_void);
}
"#,
    );
    // Both source variables can carry responsibility at different occurrences.
    // Their Owning kinds must not be mistaken for two post-copy live tokens.
    assert_kinds(
        &fixture,
        &[("f::p", SlotKind::Owning), ("f::q", SlotKind::Owning)],
    );
}

#[test]
fn ol10_mfa2_branching_reader_keeps_p_q_and_r_raw() {
    // Preserve the dossier's p -> q/r, read(q), free(r) discriminator.
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn f() -> i32 {
    let p = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *p = 1;
    let q = p;
    let r = p;
    let value = *q;
    free(r as *mut core::ffi::c_void);
    value
}
"#,
    );
    assert_kinds(
        &fixture,
        &[
            ("f::p", SlotKind::Raw),
            ("f::q", SlotKind::Raw),
            ("f::r", SlotKind::Raw),
        ],
    );
}

#[test]
fn ol11_s02_allocation_then_stack_does_not_license_the_mixed_kind_slots() {
    // Preserve both reads, both assignments and free(owner) in their source order.
    let fixture = inspect(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct Holder { ptr: *mut i32 }
pub unsafe fn f() -> i32 {
    let mut stack = 1;
    let holder = Holder { ptr: &mut stack };
    let mut p = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *p = 2;
    let owner = p;
    let mut q = p;
    let first = *q;
    p = holder.ptr;
    q = p;
    let second = *q;
    free(owner as *mut core::ffi::c_void);
    first + second
}
"#,
    );
    assert_kinds(
        &fixture,
        &[
            ("Holder.ptr", SlotKind::Raw),
            ("f::owner", SlotKind::Raw),
            ("f::p", SlotKind::Raw),
            ("f::q", SlotKind::Raw),
        ],
    );
}

#[test]
fn ol12_checked_borrowed_pair_stays_ref_ref_beside_a_fresh_return_chain() {
    let borrowed = inspect(
        r#"
pub unsafe fn borrowed(p: *mut i32) -> *mut i32 {
    let q = p;
    let before = *q;
    *p = before + 1;
    p
}
"#,
    );
    assert_kinds(
        &borrowed,
        &[
            ("borrowed::p", SlotKind::Ref),
            ("borrowed::q", SlotKind::Ref),
            ("borrowed::_0", SlotKind::Ref),
        ],
    );
    let fresh = inspect(RETURN_CHAIN);
    assert_kinds(&fresh, &[("receiver::value", SlotKind::Owning)]);
}

/// Preflight (R326-1 i): the typed hold carried by every bst and avl fold
/// declaration, so the measurement reports reasons rather than a blank.
#[test]
#[ignore = "preflight census; run explicitly"]
fn preflight_bst_avl_fold_holds() {
    const AVL: &str = r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct Avl { key: i32, left: *mut Avl, right: *mut Avl }
pub unsafe fn make(key: i32) -> *mut Avl {
    let node = malloc(core::mem::size_of::<Avl>()) as *mut Avl;
    (*node).key = key;
    (*node).left = 0 as *mut Avl;
    (*node).right = 0 as *mut Avl;
    node
}
pub unsafe fn rotate_right(y: *mut Avl) -> *mut Avl {
    let x = (*y).left;
    let subtree = (*x).right;
    (*x).right = y;
    (*y).left = subtree;
    x
}
pub unsafe fn rotate_left(x: *mut Avl) -> *mut Avl {
    let y = (*x).right;
    let subtree = (*y).left;
    (*y).left = x;
    (*x).right = subtree;
    y
}
pub unsafe fn rotate_left_right(root: *mut Avl) -> *mut Avl {
    (*root).left = rotate_left((*root).left);
    rotate_right(root)
}
pub unsafe fn rotate_right_left(root: *mut Avl) -> *mut Avl {
    (*root).right = rotate_right((*root).right);
    rotate_left(root)
}
pub unsafe fn f(left: bool) -> *mut Avl {
    let root = make(2);
    if left {
        (*root).left = make(0);
        (*(*root).left).right = make(1);
        rotate_left_right(root)
    } else {
        (*root).right = make(4);
        (*(*root).right).left = make(3);
        rotate_right_left(root)
    }
}
"#;
    for (program, code) in [("bst", BST), ("avl", AVL)] {
        super::graph_tests::with_facts(code, move |facts| {
            let declarations = facts.fold_declarations.as_deref().unwrap_or_default();
            eprintln!(
                "PREFLIGHT {program} declarations={} caller_coverage={:?}",
                declarations.len(),
                super::caller_coverage::assess(facts)
            );
            for decision in super::fold_eligibility::plan(facts).unwrap_or_default() {
                eprintln!(
                    "PREFLIGHT {program} identity {}->{} {}:{} hold={:?}",
                    decision.declaration.call.caller,
                    decision.declaration.call.callee,
                    decision.declaration.call.block,
                    decision.declaration.call.statement,
                    decision.outcome.as_ref().err()
                );
            }
            for effect in &facts.field_support_inputs.unsupported {
                eprintln!(
                    "PREFLIGHT {program} unsupported {}:{}:{} reason={} fields={:?}",
                    effect.function,
                    effect.block,
                    effect.statement,
                    effect.reason,
                    effect.field_keys
                );
            }
            // R337-2(a): every occurrence the caller gate refuses, classified.
            for declaration in facts.fold_declarations.as_deref().unwrap_or_default() {
                let call = &declaration.call;
                let Ok(refused) = super::fold_caller::unsupported_occurrences(
                    facts,
                    call,
                    &super::matched::guard_aliases(&facts.guards),
                ) else {
                    eprintln!("CALLERGATE {program} {} coverage-hold", call.caller);
                    continue;
                };
                let sites: std::collections::BTreeSet<_> = facts
                    .fold_declarations
                    .as_deref()
                    .unwrap_or_default()
                    .iter()
                    .filter(|other| other.call.caller == call.caller)
                    .map(|other| (other.call.block, other.call.statement))
                    .collect();
                let body = facts
                    .reader_inputs
                    .bodies
                    .iter()
                    .find(|b| b.function == call.caller);
                for occurrence in &refused {
                    let site = (occurrence.site.block, occurrence.site.statement);
                    let class = match &occurrence.callee {
                        Some(super::super::origin_evidence::SourceCallee::RustLibrary(_))
                            if body.is_some_and(|b| b.readonly_intrinsic(site.0, site.1)) =>
                        {
                            "read-only-intrinsic"
                        }
                        Some(super::super::origin_evidence::SourceCallee::Local(name)) => {
                            let reader = (0..4).any(|index| {
                                facts.reader_plan.lends_parameter(name, index)
                                    || facts.reader_plan.borrows_parameter(name, index)
                            });
                            if sites.contains(&site) {
                                "another-fold-site"
                            } else if reader {
                                "reader-call"
                            } else {
                                "producing-local-call"
                            }
                        }
                        _ => "other",
                    };
                    eprintln!(
                        "CALLERGATE {program} {} {}:{} class={class} callee={:?} expr={:?}",
                        call.caller,
                        occurrence.site.block,
                        occurrence.site.statement,
                        occurrence.callee,
                        occurrence.syntax.expression
                    );
                }
            }
            let members = super::fold_eligibility::member_plan(facts).unwrap_or_default();
            eprintln!("PREFLIGHT {program} member_decisions={}", members.len());
            for decision in &members {
                eprintln!(
                    "PREFLIGHT {program} member {}->{} {}:{} field={} hold={:?}",
                    decision.declaration.call.caller,
                    decision.declaration.call.callee,
                    decision.declaration.call.block,
                    decision.declaration.call.statement,
                    decision
                        .fields
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join("+"),
                    decision.outcome.as_ref().err()
                );
            }
        });
    }
}
