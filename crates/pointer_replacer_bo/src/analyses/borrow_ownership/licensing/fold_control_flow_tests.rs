//! R310-1/R315-1 witnesses for (a), realized per-path (R315-2). These target the
//! internal certificate directly, which is the surface (a) changes. Fixtures are
//! never executed.
use super::{
    facts::Facts,
    fold_internal::{self, Error},
    graph_tests::with_facts,
};

fn certify(facts: &Facts, function: &str, parameter: u32) -> Result<fold_internal::Proof, Error> {
    fold_internal::certify_linear_metadata(
        facts,
        0,
        function,
        parameter,
        &super::matched::guard_aliases(&facts.guards),
    )
}

const PRELUDE: &str = r#"
unsafe extern "C"{fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
"#;
const WIDE_PRELUDE: &str = r#"
unsafe extern "C"{fn free(p:*mut core::ffi::c_void);}
pub struct Node{left:*mut Node,right:*mut Node}
"#;

/// W-CF-1: two exit paths, each linear, agreeing on the boundary summary.
const CF1: &str = r#"
pub unsafe fn detach(node:*mut Node,pick:i32)->*mut Node {
 if pick != 0 {
  let early=(*node).child;
  free(node as *mut core::ffi::c_void);
  return early;
 }
 let late=(*node).child;
 free(node as *mut core::ffi::c_void);
 late
}
"#;

/// W-CF-2: the minValueNode view walk. The loop body performs no consuming
/// token operation, so the parameter is borrowed throughout.
const CF2: &str = r#"
pub unsafe fn minValue(mut node:*mut Node)->*mut Node {
 while !(*node).child.is_null() {
  node=(*node).child;
 }
 node
}
"#;

/// W-CF-3: a use after a conditional consume. One path frees and then reads.
const CF3: &str = r#"
pub unsafe fn detach(node:*mut Node,pick:i32)->*mut Node {
 if pick != 0 {
  free(node as *mut core::ffi::c_void);
 }
 (*node).child
}
"#;

/// W-CF-4': consumed on one path, the parameter returned on the other. Each path
/// is linear and each returns exactly one owning token.
const CF4: &str = r#"
pub unsafe fn detach(node:*mut Node,pick:i32)->*mut Node {
 if pick != 0 {
  let taken=(*node).child;
  free(node as *mut core::ffi::c_void);
  return taken;
 }
 node
}
"#;

/// W-CF-5: width. Straight-line and phi-free over a two-pointer-field struct,
/// both descendants taken, the second reattached to the first, parent freed.
const CF5: &str = r#"
pub unsafe fn detach(node:*mut Node)->*mut Node {
 let l=(*node).left;
 let r=(*node).right;
 free(node as *mut core::ffi::c_void);
 (*l).right=r;
 l
}
"#;

/// W-CF-2n: admitting a back edge is not free. This loop body frees, so the
/// loop cannot be summarised by not traversing it. K-CF-3 kills here.
const CF2N: &str = r#"
pub unsafe fn drainAll(mut node:*mut Node)->*mut Node {
 while !(*node).child.is_null() {
  let next=(*node).child;
  free(node as *mut core::ffi::c_void);
  node=next;
 }
 node
}
"#;

/// W-CF-8: a null-returning path beside token-returning paths.
const CF8: &str = r#"
pub unsafe fn deleteMaybe(node:*mut Node,pick:i32)->*mut Node {
 if node.is_null() { return node; }
 if pick != 0 {
  let taken=(*node).child;
  free(node as *mut core::ffi::c_void);
  return taken;
 }
 node
}
"#;

/// W-CF-9: a lend on one arm only. The merge's phi for the parameter has one
/// input per arm, so admitting the other arm's input would give the pre-lend
/// version two ways forward — the lend and a phi it does not sit on. K-CF-4
/// kills here.
const CF9: &str = r#"
pub unsafe fn probe(node:*mut Node,flag:i32)->*mut Node {
 if flag != 0 { let _seen=node.is_null(); }
 node
}
"#;

/// W-CF-5a: width without a second destination. Two pointer fields, the parent
/// returned with both descendants untouched — no take, no free.
const CF5A: &str = r#"
pub unsafe fn passthrough(node:*mut Node)->*mut Node {
 node
}
"#;

/// W-CF-6: the one-child deleteNode shape. It closes only with the path fact
/// that the untaken descendant is null on the taken path.
const CF6: &str = r#"
pub unsafe fn deleteOne(root:*mut Node)->*mut Node {
 if (*root).left.is_null() {
  let t=(*root).right;
  free(root as *mut core::ffi::c_void);
  return t;
 }
 root
}
"#;

/// W-CF-7: the parent is freed with an untaken descendant whose nullness is
/// unknown on that path. ParentFreeWithLiveDescendant stays load-bearing.
const CF7: &str = r#"
pub unsafe fn deleteOne(root:*mut Node,pick:i32)->*mut Node {
 if pick != 0 {
  let t=(*root).right;
  free(root as *mut core::ffi::c_void);
  return t;
 }
 root
}
"#;

#[test]
fn w_cf_1_two_linear_paths_agreeing_on_the_boundary_certify() {
    with_facts(&format!("{PRELUDE}{CF1}"), |facts| {
        certify(facts, "detach", 1).expect("both paths are linear and agree");
    });
}

#[test]
fn w_cf_2_a_view_walk_loop_certifies_as_borrowing() {
    with_facts(&format!("{PRELUDE}{CF2}"), |facts| {
        let proof = certify(facts, "minValue", 1).expect("a loop with no consuming operation");
        assert!(
            proof.actions.iter().all(|action| action.kind != "free"),
            "a view walk consumes nothing: {:?}",
            proof.actions
        );
    });
}

#[test]
fn w_cf_3_a_use_after_a_conditional_consume_is_refused() {
    with_facts(&format!("{PRELUDE}{CF3}"), |facts| {
        assert_eq!(
            certify(facts, "detach", 1),
            Err(Error::ParentFreeWithLiveDescendant),
            "the path that frees and then reads is refused for that reason"
        );
    });
}

/// W-CF-4' (R319-1): this is deleteNode's own boundary and must CERTIFY. On both
/// paths the parameter's token leaves the caller and one owning token returns;
/// which object it is is invisible to the caller, whose cell was zeroed by the
/// consuming old-zero law and whose views into the subtree are dead on every
/// path. Refusing it would refuse bst at (b).
#[test]
fn w_cf_4_prime_one_token_out_on_every_path_certifies() {
    with_facts(&format!("{PRELUDE}{CF4}"), |facts| {
        certify(facts, "detach", 1)
            .expect("one owning token returns on both paths; the object is not the contract");
    });
}

/// W-CF-8 (R319-1): a null-returning path beside token-returning paths, under a
/// nullable return. This is bst's `if (root == NULL) return root`.
#[test]
fn w_cf_8_a_null_returning_path_certifies_under_a_nullable_return() {
    with_facts(&format!("{PRELUDE}{CF8}"), |facts| {
        certify(facts, "deleteMaybe", 1).expect("a nullable return is one contract");
    });
}

#[test]
fn w_cf_9_a_lend_on_one_arm_only_certifies() {
    with_facts(&format!("{PRELUDE}{CF9}"), |facts| {
        certify(facts, "probe", 1).expect("a read on one arm moves no token");
    });
}

#[test]
fn w_cf_2n_a_loop_that_frees_is_a_typed_hold() {
    with_facts(&format!("{PRELUDE}{CF2N}"), |facts| {
        assert_eq!(
            certify(facts, "drainAll", 1),
            Err(Error::LoopWithTokenOperation),
            "a consuming loop body cannot be summarised by not traversing it"
        );
    });
}

#[test]
fn w_cf_5a_two_untouched_descendants_certify() {
    with_facts(&format!("{WIDE_PRELUDE}{CF5A}"), |facts| {
        certify(facts, "passthrough", 1)
            .expect("width alone is not the obstacle when nothing is taken");
    });
}

/// Deferred per R317-2: the second taken token needs a destination, and every
/// destination is refused by the shared pointer-destination gate. Held as a RED
/// against the G-FIELD half of that gate.
#[test]
fn w_cf_5_two_taken_descendants_certify() {
    with_facts(&format!("{WIDE_PRELUDE}{CF5}"), |facts| {
        certify(facts, "detach", 1).expect("both descendants accounted for");
    });
}

#[test]
fn w_cf_6_the_one_child_shape_certifies_on_the_path_null_fact() {
    with_facts(&format!("{WIDE_PRELUDE}{CF6}"), |facts| {
        certify(facts, "deleteOne", 1).expect("the untaken descendant is null on that path");
    });
}

#[test]
fn w_cf_7_an_untaken_descendant_of_unknown_nullness_is_refused() {
    with_facts(&format!("{WIDE_PRELUDE}{CF7}"), |facts| {
        assert_eq!(
            certify(facts, "deleteOne", 1),
            Err(Error::ParentFreeWithLiveDescendant),
            "no path fact, no close"
        );
    });
}
