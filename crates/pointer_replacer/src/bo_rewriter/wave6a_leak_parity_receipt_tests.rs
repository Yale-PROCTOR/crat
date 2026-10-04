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

/// The D4 policy of an accepted Box subject, spelled for the reconciliation.
fn policy(
    function: &str,
    name: &str,
    optional: bool,
    retained_sink: bool,
    implicit_scope_close: bool,
) -> super::verify::BoxMirDropPolicy {
    super::verify::BoxMirDropPolicy {
        subject: format!("{function}::{name}#1"),
        function: function.to_owned(),
        local_name: Some(name.to_owned()),
        overwrite_sites: Vec::new(),
        retained_sink,
        optional,
        implicit_scope_close,
    }
}

/// **R802-3 (main 166 §3) — a release at the C free site leaves no `Drop`.**
/// buffer's `buffer_free`, ht's `ht_destroy`, bst's `deleteNode`: the C free
/// is `drop(x)` of the `Option<Box<T>>` formal, which MOVES it into
/// `core::mem::drop` — a call, so the function's MIR has no `Drop` of `x`. The
/// policy allowed the empty-`Option` shell `drop(x.take())` would leave; a
/// moved `x` leaves none, and that is not an unauthorized drop.
#[test]
fn w6a_r802_a_release_by_drop_call_leaves_no_drop_terminator() {
    let source = "pub struct B { pub x: i32 }\n\
                  pub unsafe fn buffer_free(mut self_0: Option<Box<B>>) {\n\
                      let _ = self_0.as_deref_mut().unwrap().x;\n\
                      drop(self_0);\n\
                  }\n";
    let drops = super::verify::box_mir_drops_str(source).expect("observe emitted MIR drops");
    assert!(drops.is_empty(), "{drops:#?}");
    let receipt = super::verify::reconcile_box_mir_drop_policies(
        &drops,
        &[policy("buffer_free", "self_0", true, true, false)],
    );
    assert!(receipt.is_ok(), "{receipt:?}");
}

/// **Control:** a `Drop` the policy does not allow stays an error — the
/// reconciliation still refuses every unauthorized compiler-inserted drop.
#[test]
fn w6a_r802_an_unauthorized_drop_is_still_an_error() {
    let source = "pub struct B { pub x: i32 }\n\
                  pub unsafe fn f(flag: bool) -> Option<Box<B>> {\n\
                      let mut node: Box<B> = Box::new(B { x: 0 });\n\
                      if flag { return None; }\n\
                      return Some(node);\n\
                  }\n";
    let drops = super::verify::box_mir_drops_str(source).expect("observe emitted MIR drops");
    assert_eq!(drops.iter().filter(|d| !d.cleanup).count(), 1, "{drops:#?}");
    let receipt = super::verify::reconcile_box_mir_drop_policies(
        &drops,
        &[policy("f", "node", false, true, false)],
    );
    assert!(receipt.is_err(), "{receipt:?}");
}

/// **R802-3 — a certificate owner's live null return is its implicit
/// close.** quadtree's `quadtree_node_with_bounds` returns `None` with `node`
/// live (C leaks it; the callee row receipts `waiver-drop(scope-exit)`), so
/// its plan allows that one `Drop`.
#[test]
fn w6a_r802_a_certificate_owner_with_a_live_null_return_closes_at_scope_exit() {
    use super::decision::Decision;
    let _frame = super::test_model_override::frame_lock();
    let plan = ::utils::compilation::run_compiler_on_str(QUADTREE, |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let close = |function: &str, name: &str| {
            table.entries.iter().find_map(|(s, d)| match d {
                Decision::Box(plan)
                    if s.param_name.as_deref() == Some(name)
                        && tcx.item_name(s.fn_did.to_def_id()).as_str() == function =>
                {
                    Some((plan.implicit_scope_close, plan.retained_sink))
                }
                _ => None,
            })
        };
        (
            close("quadtree_node_with_bounds", "node"),
            // Control: an owner with no live null return closes nothing.
            close("quadtree_point_new", "point"),
        )
    })
    .unwrap();
    assert_eq!(plan, (Some((true, true)), Some((false, true))));
}

/// **R802-3 control (Codex):** an allowance authorizes only its own kind. A
/// policy allowing two overwrite drops and no scope-exit close does not
/// authorize a scope-exit drop — the count alone (1 ≤ 2) would.
#[test]
fn w6a_r802_an_overwrite_allowance_does_not_authorize_a_scope_exit_drop() {
    let source = "pub struct B { pub x: i32 }\n\
                  pub unsafe fn f(flag: bool) -> Option<Box<B>> {\n\
                      let mut node: Box<B> = Box::new(B { x: 0 });\n\
                      if flag { return None; }\n\
                      return Some(node);\n\
                  }\n";
    let drops = super::verify::box_mir_drops_str(source).expect("observe emitted MIR drops");
    let mut overwriting = policy("f", "node", false, false, false);
    overwriting.overwrite_sites = vec!["<o1>".to_owned(), "<o2>".to_owned()];
    let receipt = super::verify::reconcile_box_mir_drop_policies(&drops, &[overwriting]);
    assert!(receipt.is_err(), "{receipt:?}");
}

/// **R802-3 control (Codex):** a live null return widens only the owner's
/// own plan. A callee whose certificate has another Box plan of its own
/// function — here the receiver of a recursive call — keeps that plan's
/// allowance.
#[test]
fn w6a_r802_a_live_null_return_widens_only_the_owners_plan() {
    use super::decision::Decision;
    let source = r#"
#![allow(dead_code, unused_mut, unused_unsafe)]
extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; }
#[derive(Copy, Clone)]
#[repr(C)]
pub struct N { pub v: i32, pub next: *mut N }
pub unsafe extern "C" fn n_new(mut depth: i32) -> *mut N {
    let mut n = malloc(::std::mem::size_of::<N>()) as *mut N;
    if n.is_null() { return 0 as *mut N; }
    (*n).v = depth;
    (*n).next = 0 as *mut N;
    if depth > 0 as i32 {
        let mut inner = n_new(depth - 1 as i32);
        if inner.is_null() { return 0 as *mut N; }
        (*n).next = inner;
    }
    return n;
}
"#;
    let _frame = super::test_model_override::frame_lock();
    let closes = ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let mut closes = table
            .entries
            .iter()
            .filter_map(|(s, d)| match d {
                Decision::Box(plan) => Some((
                    s.param_name.clone().unwrap_or_default(),
                    plan.implicit_scope_close,
                )),
                _ => None,
            })
            .collect::<Vec<_>>();
        closes.sort();
        closes
    })
    .unwrap();
    // `n` is live at `inner`'s null return (C leaks it): its close. `inner`
    // is `None` there and stored before the other exit: no close of its own.
    assert!(
        closes.iter().all(|(name, close)| *close == (name == "n")),
        "{closes:?}"
    );
}
