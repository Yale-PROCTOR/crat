//! wave-6a relay 143 (R792-4): the leak-parity waiver's receipts are exactly
//! its implicit closes (addendum 101's discipline). A close is a path end at
//! which an owner is live and the input neither released nor moved it; each
//! one carries one `waiver-drop(..)` row naming its site and its owner, so the
//! census counts the closes by kind from the receipts alone.

use super::wave6a_allocation_tests::emitted;

const QUADTREE: &str = include_str!("testdata/w6a-r776-quadtree.rs");

/// `(function, line of the exit, owner)` of every `waiver-drop(scope-exit)`
/// row that names an owner.
fn closes(receipts: &str) -> Vec<(String, usize, String)> {
    let mut rows = receipts
        .lines()
        .filter_map(|line| {
            let mut columns = line.split('\t');
            let function = columns.next()?;
            let detail = columns.nth(1)?;
            let rest = detail.strip_prefix("waiver-drop(scope-exit) site=")?;
            let (site, owner) = rest.rsplit_once(" receiver=")?;
            let line = site.split(':').nth(1)?.parse().ok()?;
            Some((function.to_owned(), line, owner.to_owned()))
        })
        .collect::<Vec<_>>();
    rows.sort();
    rows
}

/// **The RED (R792-4 item 1).** quadtree's `split_node_` allocates four
/// children before it stores any. At `ne`'s, `sw`'s and `se`'s null returns
/// (corpus lines 364, 369, 374) the children allocated so far still own: C
/// leaks them, the emitted `Option<Box>` drops them. Three sites, six closes,
/// one row each. `se` is stored before every exit it reaches; a child's own
/// null return holds its `None`.
#[test]
fn w6a_r792_split_node_receipts_each_live_owner_at_each_exit() {
    let _frame = super::test_model_override::frame_lock();
    let out = emitted("r792-quadtree", QUADTREE);
    let receipts = &out.artifacts.return_certificate_receipts;
    let split = closes(receipts)
        .into_iter()
        .filter(|(function, _, _)| function.ends_with("::split_node_"))
        .map(|(_, line, owner)| (line, owner))
        .collect::<Vec<_>>();
    assert_eq!(
        split,
        [
            (364, "nw".to_owned()),
            (369, "ne".to_owned()),
            (369, "nw".to_owned()),
            (374, "ne".to_owned()),
            (374, "nw".to_owned()),
            (374, "sw".to_owned()),
        ],
        "{receipts}"
    );
    // R776-5's hand-over makes one more: `quadtree_insert`'s point is handed
    // to `insert_` at its last use, but its `node_contains_` return (459)
    // comes first and holds it; C leaks it there.
    assert!(
        closes(receipts).contains(&(
            "src::src::quadtree::quadtree_insert".to_owned(),
            459,
            "point".to_owned()
        )),
        "{receipts}"
    );
    // No owner-less scope-exit row is left for a receiver: every row names
    // its site and its owner.
    assert!(
        !receipts
            .lines()
            .any(|l| l.contains("\treceiver\t") && !l.contains(" receiver=")),
        "{receipts}"
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
}

const ITEM: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
#[repr(C)]
pub struct item { pub id: i32 }
#[repr(C)]
pub struct slot { pub it: *mut item }
pub unsafe extern "C" fn item_new(mut id: i32) -> *mut item {
    let mut it = malloc(::std::mem::size_of::<item>()) as *mut item;
    if it.is_null() {
        return 0 as *mut item;
    }
    (*it).id = id;
    return it;
}
"#;

/// The Codex review's `break` (R792-4): the owner outlives the loop, so the
/// `break` does not leave its scope. The stored path's `return` holds
/// nothing (`it` moved), the null guard's holds `None`, and the final
/// `return` (line 33), reached through the `break` or the loop's end, holds
/// `it`: one row.
#[test]
fn w6a_r792_a_break_inside_the_owners_scope_is_not_an_exit() {
    let source = format!(
        "{ITEM}{}",
        r#"pub unsafe extern "C" fn f(mut s: *mut slot, mut c: i32) -> i32 {
    let mut it = item_new(c);
    if it.is_null() {
        return 0 as i32;
    }
    while c > 0 as i32 {
        if c == 3 as i32 {
            break;
        }
        if c == 5 as i32 {
            (*s).it = it;
            return 1 as i32;
        }
        c -= 1;
    }
    return 2 as i32;
}
"#
    );
    let out = emitted("r792-break", &source);
    let receipts = &out.artifacts.return_certificate_receipts;
    assert_eq!(
        closes(receipts)
            .into_iter()
            .map(|(_, line, owner)| (line, owner))
            .collect::<Vec<_>>(),
        [(33, "it".to_owned())],
        "{receipts}\n{}",
        out.source
    );
}

/// The Codex review's negated guard (R792-4): `if !it.is_null() { continue; }`
/// keeps `it` on the `continue` edge only; the loop body's end (line 27)
/// closes it, and the `return` after the guard holds `None`.
#[test]
fn w6a_r792_a_negated_own_guard_closes_at_the_body_end() {
    let source = format!(
        "{ITEM}{}",
        r#"pub unsafe extern "C" fn f(mut n: i32) {
    let mut i = 0 as i32;
    while i < n {
        let mut it = item_new(i);
        i += 1;
        if !it.is_null() {
            continue;
        }
        return;
    }
}
"#
    );
    let out = emitted("r792-negated", &source);
    let receipts = &out.artifacts.return_certificate_receipts;
    assert_eq!(
        closes(receipts)
            .into_iter()
            .map(|(_, line, owner)| (line, owner))
            .collect::<Vec<_>>(),
        [(27, "it".to_owned())],
        "{receipts}\n{}",
        out.source
    );
}
