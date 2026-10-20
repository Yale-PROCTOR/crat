//! R310-2/R317-2 witnesses for (b): the return-to-cell store, which is the
//! shape `root->left = insert(root->left, key)` and the shape that holds
//! W-CF-5. Staged RED-first: what refuses, and with which named reason, is the
//! measurement. Fixtures are never executed.
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
pub unsafe fn step(node:*mut Node)->*mut Node{node}
"#;
const WIDE_PRELUDE: &str = r#"
unsafe extern "C"{fn free(p:*mut core::ffi::c_void);}
pub struct Node{left:*mut Node,right:*mut Node}
pub unsafe fn step(node:*mut Node)->*mut Node{node}
"#;

/// W-RC-1: the return-to-cell store with no recursion. `step` already has the
/// licensed contract — one token in, one token out — so the only new thing here
/// is that the result goes back into the cell it was read from.
const RC1: &str = r#"
pub unsafe fn descend(root:*mut Node)->*mut Node{
 (*root).child=step((*root).child);
 root
}
"#;

/// W-RC-2: the same store, self-recursive. This is bst's `insert`. Under
/// assume-guarantee the callee's contract is the one being proved.
const RC2: &str = r#"
pub unsafe fn insert(root:*mut Node,key:i32)->*mut Node{
 if root.is_null(){ return root; }
 (*root).child=insert((*root).child,key);
 root
}
"#;

/// W-RC-3: the token read from one cell is stored into another, leaving the
/// first cell still naming an object nothing is responsible for. Duplicated
/// responsibility; must be refused however the store is admitted.
const RC3: &str = r#"
pub unsafe fn crossed(root:*mut Node)->*mut Node{
 (*root).right=step((*root).left);
 root
}
"#;

/// W-RC-5: the null path returns a freshly made object rather than the
/// parameter. This is bst's `if (node == NULL) return newNode(key);` at width
/// one — the shape that holds the era-5b target.
const ALLOC_PRELUDE: &str = r#"
unsafe extern "C"{
 fn free(p:*mut core::ffi::c_void);
 fn malloc(size:usize)->*mut core::ffi::c_void;
}
pub struct Node{child:*mut Node}
pub unsafe fn fresh()->*mut Node{
 let n=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*n).child=0 as *mut Node;
 n
}
"#;
const RC5: &str = r#"
pub unsafe fn insertFresh(root:*mut Node,key:i32)->*mut Node{
 if root.is_null(){ return fresh(); }
 (*root).child=insertFresh((*root).child,key);
 root
}
"#;

/// W-RC-6: mutual recursion. `ping` needs `pong`'s contract and `pong` needs
/// `ping`'s, so neither is established and the pair is a typed hold. Recorded
/// as a must-not-move because it is the shape the `visiting` set exists for:
/// without it this does not refuse, it fails to terminate, which is why its
/// killer is not runnable and the guard is justified structurally instead.
const RC6: &str = r#"
pub unsafe fn ping(root:*mut Node,key:i32)->*mut Node{
 if root.is_null(){ return root; }
 (*root).child=pong((*root).child,key);
 root
}
pub unsafe fn pong(root:*mut Node,key:i32)->*mut Node{
 if root.is_null(){ return root; }
 (*root).child=ping((*root).child,key);
 root
}
"#;

/// W-RC-3r: the live counterpart of W-RC-3. Recursive, so the assumed contract
/// is in play, and the token read from `left` is stored into `right` — leaving
/// `left` naming an object nothing is responsible for and dropping whatever
/// `right` held. Must be refused. K-RC-2 kills here.
const RC3R: &str = r#"
pub unsafe fn crossed(root:*mut Node,key:i32)->*mut Node{
 if root.is_null(){ return root; }
 (*root).right=crossed((*root).left,key);
 root
}
"#;

/// W-RC-4: a callee that returns no token at all, its result stored back into
/// the cell. The cell's own token went in and nothing came out, so the object
/// is lost. `leak` is not the function under proof, so no contract is assumed
/// for it — and K-RC-1, which assumes every callee's, dies here.
const RC4: &str = r#"
pub unsafe fn leak(node:*mut Node)->*mut Node{ 0 as *mut Node }
pub unsafe fn dropIn(root:*mut Node)->*mut Node{
 (*root).child=leak((*root).child);
 root
}
"#;

/// Census only, never a gate: does the member fold chain already reach the
/// return-to-cell shape, and with which hold? The internal certificate and the
/// member chain are different surfaces, and (b)'s design turns on whether the
/// link across the call has to be built or only joined.
#[test]
#[ignore]
fn census_b_member_chain_on_the_return_to_cell_shape() {
    for (name, code) in [
        ("rc1", format!("{PRELUDE}{RC1}")),
        ("rc2", format!("{PRELUDE}{RC2}")),
    ] {
        with_facts(&code, move |facts| {
            let declarations = facts.fold_declarations.as_deref().unwrap_or_default();
            eprintln!(
                "CENSUS {name} declarations={} caller_coverage={:?}",
                declarations.len(),
                super::caller_coverage::assess(facts)
            );
            for decision in super::fold_eligibility::plan(facts).unwrap_or_default() {
                eprintln!(
                    "CENSUS {name} identity {}->{} {}:{} hold={:?}",
                    decision.declaration.call.caller,
                    decision.declaration.call.callee,
                    decision.declaration.call.block,
                    decision.declaration.call.statement,
                    decision.outcome.as_ref().err()
                );
            }
            let members = super::fold_eligibility::member_plan(facts).unwrap_or_default();
            eprintln!("CENSUS {name} member_decisions={}", members.len());
            for decision in members {
                eprintln!("CENSUS {name} member {decision:?}");
            }
        });
    }
}

#[test]
fn w_rc_1_the_return_to_cell_store_certifies() {
    with_facts(&format!("{PRELUDE}{RC1}"), |facts| {
        certify(facts, "descend", 1).expect("one token out of the cell and one back in");
    });
}

#[test]
fn w_rc_2_the_recursive_return_to_cell_store_certifies() {
    with_facts(&format!("{PRELUDE}{RC2}"), |facts| {
        certify(facts, "insert", 1).expect("assume-guarantee on the licensed contract");
    });
}

#[test]
fn w_rc_5_a_null_path_returning_a_fresh_object_certifies() {
    with_facts(&format!("{ALLOC_PRELUDE}{RC5}"), |facts| {
        certify(facts, "insertFresh", 1)
            .expect("a null parameter owes nothing and the fresh token takes nothing");
    });
}

#[test]
fn w_rc_6_mutual_recursion_is_a_typed_hold() {
    with_facts(&format!("{PRELUDE}{RC6}"), |facts| {
        assert!(
            certify(facts, "ping", 1).is_err(),
            "neither contract can be assumed to establish the other"
        );
    });
}

#[test]
fn w_rc_3r_a_recursive_cross_cell_store_is_refused() {
    with_facts(&format!("{WIDE_PRELUDE}{RC3R}"), |facts| {
        assert!(
            certify(facts, "crossed", 1).is_err(),
            "the read cell is left naming an object nothing is responsible for"
        );
    });
}

#[test]
fn w_rc_4_a_callee_that_returns_no_token_is_refused() {
    with_facts(&format!("{PRELUDE}{RC4}"), |facts| {
        assert!(
            certify(facts, "dropIn", 1).is_err(),
            "no contract is assumed for a callee that is not under proof"
        );
    });
}

#[test]
fn w_rc_3_a_cross_cell_store_is_refused() {
    with_facts(&format!("{WIDE_PRELUDE}{RC3}"), |facts| {
        assert!(
            certify(facts, "crossed", 1).is_err(),
            "the read cell is left naming an object nothing is responsible for"
        );
    });
}
