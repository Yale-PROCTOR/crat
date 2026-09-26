//! R310-3 witnesses for (c): a borrowing callee's contract at a call boundary.
//! Staged RED-first. These are the shapes report 016 measured as holding bst's
//! remaining `deleteNode` path and both of avl's rotations. Fixtures are never
//! executed.
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
pub unsafe fn minValue(mut node:*mut Node)->*mut Node{
 while !(*node).child.is_null(){ node=(*node).child; }
 node
}
"#;
const WIDE_PRELUDE: &str = r#"
unsafe extern "C"{fn free(p:*mut core::ffi::c_void);}
pub struct Node{left:*mut Node,right:*mut Node}
"#;

/// W-VW-1: the shape that holds bst's last `deleteNode` path. `minValue`
/// borrows — it walks a view and hands one back — so the component it was given
/// is still the caller's afterwards. Modelled as a move, the token lands in `v`
/// and is dropped while `(*root).child` still names it.
const VW1: &str = r#"
pub unsafe fn peek(root:*mut Node)->*mut Node{
 let v=minValue((*root).child);
 let _seen=v.is_null();
 root
}
"#;

/// W-VW-2: avl's rotation. The parameter is stored **into its own descendant's**
/// field and the descendant is returned, with a grandchild read in between.
const VW2: &str = r#"
pub unsafe fn rotate(x:*mut Node)->*mut Node{
 let y=(*x).right;
 let subtree=(*y).left;
 (*y).left=x;
 (*x).right=subtree;
 y
}
"#;

/// W-VW-3: a borrowed view stored into a cell. **This certifies today, and the
/// expectation below is the one I am least sure of.** Both readings are in
/// report 017; the short version is that `root->child = minValue(root->child)`
/// makes the cell name a node deep inside its own old subtree, and the spine
/// above it becomes unreachable. That is a *leak*, which the input program
/// commits too and which crat owes no parity on — not a double free, since
/// nothing reachable still names the skipped nodes. If that reading holds the
/// assertion below is wrong and this becomes a positive. Staged as written so
/// the question is visible rather than settled by whichever way I happened to
/// write it.
const VW3: &str = r#"
pub unsafe fn stash(root:*mut Node)->*mut Node{
 (*root).child=minValue((*root).child);
 root
}
"#;

/// W-VW-4 (R336-2): a lent view SUNK. `minValue` only lent the component, so
/// the caller still owns it; freeing the view frees a subtree the caller is
/// still responsible for, and on the emitted side it is a `free` through what
/// became a borrow into a `Box`. Must refuse.
const VW4: &str = r#"
pub unsafe fn dropView(root:*mut Node)->*mut Node{
 let v=minValue((*root).child);
 free(v as *mut core::ffi::c_void);
 root
}
"#;

/// W-VW-5 (R336-2): a view THROUGH A WRAPPER. `hop` hands back what `minValue`
/// lent it, so `hop`'s own return is a view; storing it into an owning cell is
/// W-VW-3 one call further out. Must refuse, and `hop`'s classification is the
/// thing to measure.
const VW5: &str = r#"
pub unsafe fn hop(root:*mut Node)->*mut Node{ minValue((*root).child) }
pub unsafe fn wrap(root:*mut Node)->*mut Node{
 (*root).child=hop(root);
 root
}
"#;

#[test]
fn w_vw_4_a_lent_view_that_is_sunk_is_refused() {
    with_facts(&format!("{PRELUDE}{VW4}"), |facts| {
        assert_eq!(
            certify(facts, "dropView", 1),
            Err(Error::Unsupported(fold_internal::Site::SinkOnView)),
            "a lent component is still the caller's and may not be freed here"
        );
    });
}

#[test]
fn w_vw_5_a_view_through_a_wrapper_is_refused() {
    with_facts(&format!("{PRELUDE}{VW5}"), |facts| {
        eprintln!(
            "VW5 hop lends={} borrows={}",
            facts.reader_plan.lends_parameter("hop", 0),
            facts.reader_plan.borrows_parameter("hop", 0)
        );
        assert_eq!(
            certify(facts, "wrap", 1),
            Err(Error::Unsupported(
                fold_internal::Site::ViewStoredIntoOwningCell
            )),
            "a view does not become a token by passing through another function"
        );
    });
}

/// W-VW-2n-d (R337-3(ii)): `x` lands at `y.left` with its own `right` cell
/// consumed and never refilled. In C that cell still holds `y` — a cycle, and
/// UB-free — but the model consumes on read and the emitted owning form moves
/// the token out, so a later read of `y.left.right` sees `y` in C and nothing in
/// the emitted program. That divergence is outside §28, so a landed object's
/// consumed, unrefilled cell must refuse. Measured at depth one first, per the
/// ruling, before any depth-2 machinery exists.
const VW2ND: &str = r#"
pub unsafe fn twist(x:*mut Node)->*mut Node{
 let y=(*x).right;
 (*y).left=x;
 y
}
"#;

#[test]
fn w_vw_2n_d_a_landed_object_with_a_consumed_unrefilled_cell_is_refused() {
    with_facts(&format!("{WIDE_PRELUDE}{VW2ND}"), |facts| {
        assert_eq!(
            certify(facts, "twist", 1),
            Err(Error::Unsupported(
                fold_internal::Site::ConsumedCellNotRefilled
            )),
            "a cell consumed and not refilled diverges from the input on a later read"
        );
    });
}

#[test]
fn w_vw_1_a_borrowed_view_that_is_dropped_certifies() {
    with_facts(&format!("{PRELUDE}{VW1}"), |facts| {
        certify(facts, "peek", 1).expect("a lent component is still the caller's");
    });
}

#[test]
fn w_vw_2_the_rotation_certifies() {
    with_facts(&format!("{WIDE_PRELUDE}{VW2}"), |facts| {
        certify(facts, "rotate", 1).expect("the parameter is folded under its own descendant");
    });
}

#[test]
fn w_vw_3_a_borrowed_view_stored_into_a_cell_is_refused() {
    with_facts(&format!("{PRELUDE}{VW3}"), |facts| {
        assert!(
            certify(facts, "stash", 1).is_err(),
            "a lent component cannot also become owned cell content"
        );
    });
}
