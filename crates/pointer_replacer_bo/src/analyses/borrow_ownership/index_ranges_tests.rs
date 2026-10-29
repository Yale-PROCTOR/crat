//! Witnesses of the index-range discharge (relay era-5c/267 §2, report 218 §4
//! with the seat's riders R1–R5). Every fixture function is `unsafe extern "C"`,
//! as C2Rust's are: in a Rust-ABI body the retirement review rejects every
//! stack-local loan live across an `unwind continue` call (report 217 §2), which
//! would mask the edge under test.
//!
//! The end-to-end assertion is the guarded repair's own: `model_accepts` on a
//! model whose named slots are `Ref` and every other slot `Raw`, the conflict
//! edges of the function (`borrow_conflicts`, every pointer local of the
//! function a candidate), and, on the positives, the `range-disjoint` receipt.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{Body, Local, Operand, Rvalue, StatementKind};
use rustc_span::def_id::LocalDefId;

use super::{
    SlotKind, borrow_engine, borrow_verify,
    coherence::CopyLendPair,
    crate_slots::CrateSlots,
    index_ranges::{self, Bound, Footprint, IndexRanges, RangeDisjoint},
    slots::SlotId,
    solver::SlotRef,
    source_events,
};
use crate::utils::rustc::RustProgram;

fn with_program<R: Send>(code: &str, f: impl FnOnce(&RustProgram<'_>) -> R + Send) -> R {
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
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        f(&program)
    })
    .unwrap_or_else(|error| error.raise())
}

fn function(program: &RustProgram<'_>, name: &str) -> LocalDefId {
    let found: Vec<_> = program
        .functions
        .iter()
        .copied()
        .filter(|f| program.tcx.item_name(f.to_def_id()).as_str() == name)
        .collect();
    assert_eq!(found.len(), 1, "exactly one function {name}");
    found[0]
}

/// The pointer locals of a body, the return place excepted.
fn pointer_locals(body: &Body<'_>) -> Vec<Local> {
    body.local_decls
        .iter_enumerated()
        .filter(|(local, decl)| local.as_u32() != 0 && decl.ty.is_any_ptr())
        .map(|(local, _)| local)
        .collect()
}

/// The locals assigned `copy source` (or `move source`), in order.
fn copies_of(body: &Body<'_>, source: Local) -> Vec<Local> {
    let mut out = Vec::new();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            if let StatementKind::Assign(box (
                place,
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p)),
            )) = &statement.kind
                && p.as_local() == Some(source)
                && let Some(local) = place.as_local()
            {
                out.push(local);
            }
        }
    }
    out
}

/// The model: every slot `Raw`, then every depth-0 slot of `name`'s pointer
/// locals `Ref`, except the `owning` ones, `Owning`.
fn model(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    name: &str,
    owning: &[Local],
) -> FxHashMap<SlotRef, SlotKind> {
    let mut model = FxHashMap::default();
    for index in 0..slots.field_slots.len() {
        model.insert(SlotRef::Field(SlotId::from_usize(index)), SlotKind::Raw);
    }
    for (&f, universe) in &slots.fn_local_slots {
        for index in 0..universe.len() {
            model.insert(SlotRef::Local(f, SlotId::from_usize(index)), SlotKind::Raw);
        }
    }
    let f = function(program, name);
    let body = program
        .tcx
        .mir_drops_elaborated_and_const_checked(f)
        .borrow();
    for local in pointer_locals(&body) {
        let Some(slot) = slots.fn_local_slots[&f].slot_for_local_depth(local, 0) else {
            continue;
        };
        let kind = if owning.contains(&local) {
            SlotKind::Owning
        } else {
            SlotKind::Ref
        };
        model.insert(SlotRef::Local(f, slot), kind);
    }
    model
}

/// Does the guarded repair accept `name`'s pointer locals as `Ref`? The
/// receipts recorded on the way are returned with the verdict.
fn accepts(code: &str, name: &str) -> (bool, Vec<RangeDisjoint>) {
    with_program(code, |program| {
        let slots = CrateSlots::build(program);
        let model = model(program, &slots, name, &[]);
        let inventory = std::sync::Arc::new(source_events::collect(program));
        let _ = index_ranges::take_receipts();
        let accepted = source_events::with_inventory(&inventory, || {
            borrow_verify::model_accepts(program, &slots, &model, true)
        });
        (accepted, index_ranges::take_receipts())
    })
}

/// The conflict edges in `name`, every pointer local of `name` a candidate.
fn edges(code: &str, name: &str) -> usize {
    with_program(code, |program| {
        let target = function(program, name);
        let candidates: FxHashMap<LocalDefId, FxHashSet<Local>> = program
            .functions
            .iter()
            .map(|&f| {
                let body = program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(f)
                    .borrow();
                let locals = if f == target {
                    pointer_locals(&body).into_iter().collect()
                } else {
                    FxHashSet::default()
                };
                (f, locals)
            })
            .collect();
        let conflicts = borrow_engine::borrow_conflicts(
            program,
            |f: LocalDefId| {
                let set = candidates[&f].clone();
                move |local: Local| set.contains(&local)
            },
            |_: LocalDefId| |_: Local| true,
        );
        conflicts.get(&target).map_or(0, Vec::len)
    })
}

/// Is there a receipt on the first formal with these byte ranges? (One
/// invalidation is skipped per (access, loan) the engine checks, live there or
/// not; a disjoint pair is skipped both ways.)
fn has_receipt(receipts: &[RangeDisjoint], loan: (i64, i64), access: (i64, i64)) -> bool {
    receipts.iter().any(|receipt| {
        receipt.base.as_u32() == 1
            && receipt.loan_bytes == Some(loan)
            && receipt.access_bytes == Some(access)
    })
}

/// A control: the edge is there, the function is not accepted, and no
/// invalidation in the program was skipped.
fn control(code: &str, name: &str) {
    assert!(edges(code, name) > 0, "the control's edge is there");
    let (accepted, receipts) = accepts(code, name);
    assert!(!accepted, "the control is not accepted");
    assert!(receipts.is_empty(), "no discharge: {receipts:?}");
}

/// The `lengths` shape (005's `SPX_chain_lengths`, `wots_checksum`, `base_w`):
/// `check` reads `head[i]` for `i < LEN1` (`wrapping_add`), and hands `tail` to
/// `fill`, which writes `out[j]` for `k < n` with `j` and `k` stepping together.
const X1: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_upper_case_globals)]
pub const SPX_N: core::ffi::c_int = 16 as core::ffi::c_int;
pub const LOGW: core::ffi::c_int = 4 as core::ffi::c_int;
pub const LEN1: core::ffi::c_int = 8 as core::ffi::c_int * SPX_N / LOGW;
pub const LEN2: core::ffi::c_int = 3 as core::ffi::c_int;
unsafe extern "C" fn fill(mut out: *mut core::ffi::c_uint, n: core::ffi::c_int) {
    let mut j: core::ffi::c_int = 0 as core::ffi::c_int;
    let mut k: core::ffi::c_int = 0;
    k = 0 as core::ffi::c_int;
    while k < n {
        *out.offset(j as isize) = 7 as core::ffi::c_uint;
        j += 1;
        k += 1;
    }
}
unsafe extern "C" fn check(mut tail: *mut core::ffi::c_uint, mut head: *const core::ffi::c_uint) {
    let mut s: core::ffi::c_uint = 0 as core::ffi::c_uint;
    let mut i: core::ffi::c_uint = 0;
    i = 0 as core::ffi::c_uint;
    while i < LEN1 as core::ffi::c_uint {
        s = s.wrapping_add(*head.offset(i as isize));
        i = i.wrapping_add(1);
    }
    fill(tail, LEN2);
}
#[no_mangle]
pub unsafe extern "C" fn split(mut v: *mut core::ffi::c_uint) {
    check(v.offset(LEN1 as isize), v);
}
"#;

/// X1: the two views reach `[128, 140)` (written) and `[0, 128)` (read) of `v`:
/// the edge is gone, the function's pointers are `Ref`, and the receipt names
/// both ranges.
#[test]
fn e5c_w267_x1_two_views_disjoint_constant_ranges_both_ref() {
    assert_eq!(edges(X1, "split"), 0, "the disjoint pair leaves no edge");
    let (accepted, receipts) = accepts(X1, "split");
    assert!(accepted, "`split`'s pointers are Ref");
    assert!(
        has_receipt(&receipts, (128, 140), (0, 128)),
        "the receipt: base `v`, the loan's [128, 140), the access's [0, 128)"
    );
}

/// X2: one element further in, `[124, 136)` meets `[0, 128)`: the edge stays.
#[test]
fn e5c_w267_x2_overlapping_ranges_keep_the_edge() {
    let code = X1.replace(
        "check(v.offset(LEN1 as isize), v);",
        "check(v.offset(31), v);",
    );
    control(&code, "split");
}

/// X3: a delta that is a formal is no constant: Unknown, the edge stays.
#[test]
fn e5c_w267_x3_non_constant_delta_is_unknown() {
    let code = X1.replace(
        "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint) {\n    check(v.offset(LEN1 as isize), v);",
        "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint, k: core::ffi::c_int) {\n    check(v.offset(k as isize), v);",
    );
    assert!(code.contains("k as isize"));
    control(&code, "split");
}

/// X4: a foreign callee without a row is Unknown: the edge stays.
#[test]
fn e5c_w267_x4_foreign_callee_is_unknown() {
    const CODE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables)]
unsafe extern "C" {
    fn check_elsewhere(tail: *mut core::ffi::c_uint, head: *const core::ffi::c_uint);
}
#[no_mangle]
pub unsafe extern "C" fn split(mut v: *mut core::ffi::c_uint) {
    check_elsewhere(v.offset(32), v);
}
"#;
    control(CODE, "split");
}

/// X4b: `memset` with a constant length is its row: `check` clears `tail[0, 3)`
/// and reads `head[0, 32)`: `[128, 140)` written against `[0, 128)` read, the
/// edge is gone.
#[test]
fn e5c_w267_x4b_memset_row_with_a_constant_length() {
    let code = X1.replace(
        "    fill(tail, LEN2);",
        "    memset(tail as *mut core::ffi::c_void, 0, 12 as core::ffi::c_ulong);",
    ) + "unsafe extern \"C\" {\n    fn memset(s: *mut core::ffi::c_void, c: core::ffi::c_int, n: core::ffi::c_ulong) -> *mut core::ffi::c_void;\n}\n";
    assert!(code.contains("memset(tail"));
    assert_eq!(edges(&code, "split"), 0);
    let (accepted, receipts) = accepts(&code, "split");
    assert!(accepted);
    assert!(has_receipt(&receipts, (128, 140), (0, 128)));
}

/// X4c (the review's M1): bytes copied out of the base by `memcpy` may be a
/// pointer to it, used after through the copy: the source row is Unknown and
/// the edge stays.
#[test]
fn e5c_w267_x4c_memcpy_source_is_unknown() {
    const CODE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables)]
unsafe extern "C" {
    fn memcpy(
        dest: *mut core::ffi::c_void,
        src: *const core::ffi::c_void,
        n: core::ffi::c_ulong,
    ) -> *mut core::ffi::c_void;
}
#[no_mangle]
pub unsafe extern "C" fn split(mut v: *mut core::ffi::c_uint) {
    memcpy(
        v.offset(32) as *mut core::ffi::c_void,
        v as *const core::ffi::c_void,
        12 as core::ffi::c_ulong,
    );
}
"#;
    control(CODE, "split");
}

/// X1b (the review's M3): `head` is `*mut`, so `v` reaches the call by a copy
/// the engine checks at the call (a deferred argument read): the discharge
/// reads it at its statement, and the edge is gone.
#[test]
fn e5c_w267_x1b_a_deferred_argument_read() {
    let code = X1.replace(
        "unsafe extern \"C\" fn check(mut tail: *mut core::ffi::c_uint, mut head: *const core::ffi::c_uint) {",
        "unsafe extern \"C\" fn check(mut tail: *mut core::ffi::c_uint, mut head: *mut core::ffi::c_uint) {",
    );
    assert!(code.contains("mut head: *mut"));
    assert_eq!(edges(&code, "split"), 0);
    let (accepted, receipts) = accepts(&code, "split");
    assert!(accepted);
    assert!(has_receipt(&receipts, (128, 140), (0, 128)));
}

/// X1c: the head first, `check_rev(v, v.offset(32))`: the loan is the read
/// view's, the access the written one's; the edge is gone.
#[test]
fn e5c_w267_x1c_the_read_view_first() {
    let code = X1
        .replace(
            "unsafe extern \"C\" fn check(mut tail: *mut core::ffi::c_uint, mut head: *const core::ffi::c_uint) {",
            "unsafe extern \"C\" fn check(mut head: *const core::ffi::c_uint, mut tail: *mut core::ffi::c_uint) {",
        )
        .replace("check(v.offset(LEN1 as isize), v);", "check(v, v.offset(LEN1 as isize));");
    assert!(code.contains("check(v, v.offset"));
    assert_eq!(edges(&code, "split"), 0);
    let (accepted, receipts) = accepts(&code, "split");
    assert!(accepted);
    assert!(has_receipt(&receipts, (0, 128), (128, 140)));
}

/// X5: `fill`'s bound is `check`'s own formal `m`, and `split` passes the
/// constant 3: instantiated two levels up, the edge is gone.
#[test]
fn e5c_w267_x5_extent_through_a_nested_local_callee() {
    let code = X1
        .replace(
            "unsafe extern \"C\" fn check(mut tail: *mut core::ffi::c_uint, mut head: *const core::ffi::c_uint) {",
            "unsafe extern \"C\" fn check(mut tail: *mut core::ffi::c_uint, mut head: *const core::ffi::c_uint, m: core::ffi::c_int) {",
        )
        .replace("fill(tail, LEN2);", "fill(tail, m);")
        .replace("check(v.offset(LEN1 as isize), v);", "check(v.offset(LEN1 as isize), v, 3);");
    assert!(code.contains("fill(tail, m)") && code.contains("v, 3)"));
    assert_eq!(edges(&code, "split"), 0);
    let (accepted, receipts) = accepts(&code, "split");
    assert!(accepted);
    assert!(has_receipt(&receipts, (128, 140), (0, 128)));
}

/// X6: the read bound is `split2`'s own formal: `[0, 4n)` is symbolic at the
/// conflict, so Unknown, and the edge stays.
#[test]
fn e5c_w267_x6_loop_bound_from_a_non_constant_actual_is_unknown() {
    const CODE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments)]
unsafe extern "C" fn check2(
    mut tail: *mut core::ffi::c_uint,
    mut head: *const core::ffi::c_uint,
    n: core::ffi::c_int,
) {
    let mut s: core::ffi::c_uint = 0;
    let mut i: core::ffi::c_int = 0;
    while i < n {
        s = s.wrapping_add(*head.offset(i as isize));
        i += 1;
    }
    *tail = s;
}
#[no_mangle]
pub unsafe extern "C" fn split2(mut v: *mut core::ffi::c_uint, n: core::ffi::c_int) {
    check2(v.offset(32), v, n);
}
"#;
    control(CODE, "split2");
}

/// X7a: a pointer with two definitions has no base: the edge stays.
#[test]
fn e5c_w267_x7a_two_definitions_never_discharge() {
    let code = X1.replace(
        "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint) {\n    check(v.offset(LEN1 as isize), v);",
        "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint, mut w: *mut core::ffi::c_uint, c: core::ffi::c_int) {\n    let mut p: *mut core::ffi::c_uint = if c != 0 { v } else { w };\n    check(p.offset(LEN1 as isize), v);",
    );
    assert!(code.contains("if c != 0"));
    control(&code, "split");
}

/// X7b: two formals are two bases, whatever their ranges: the table roots the
/// two values at different formals, and the discharge compares only one base.
#[test]
fn e5c_w267_x7b_two_bases_never_discharge() {
    const CODE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables)]
unsafe extern "C" fn check(mut tail: *mut core::ffi::c_uint, mut head: *const core::ffi::c_uint) {
    *tail = *head;
}
#[no_mangle]
pub unsafe extern "C" fn g(mut a: *mut core::ffi::c_uint, mut b: *mut core::ffi::c_uint) {
    check(a.offset(32), b);
}
"#;
    with_program(CODE, |program| {
        let table = IndexRanges::build(program);
        let g = function(program, "g");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(g)
            .borrow();
        let a = Local::from_u32(1);
        let b = Local::from_u32(2);
        let from_a = copies_of(&body, a)[0];
        let from_b = copies_of(&body, b)[0];
        assert_eq!(table.family(g, from_a).map(|(root, _)| root), Some(a));
        assert_eq!(table.family(g, from_b).map(|(root, _)| root), Some(b));
    });
}

/// X8: `fill` recurses: a recursive callee's extent is Unknown, the edge stays.
#[test]
fn e5c_w267_x8_recursion_is_unknown() {
    let code = X1.replace(
        "    k = 0 as core::ffi::c_int;\n    while k < n {\n        *out.offset(j as isize) = 7 as core::ffi::c_uint;\n        j += 1;\n        k += 1;\n    }",
        "    if n > 0 {\n        *out = 7 as core::ffi::c_uint;\n        fill(out.offset(1), n - 1);\n    }",
    );
    assert!(code.contains("fill(out.offset(1), n - 1)"));
    control(&code, "split");
}

/// X9: the issuer's value is stored into a struct before the call: it escapes,
/// Unknown, the edge stays.
#[test]
fn e5c_w267_x9_escape_is_unknown() {
    let code = X1.replace(
        "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint) {\n    check(v.offset(LEN1 as isize), v);",
        "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint, mut keep: *mut Keep) {\n    let mut t: *mut core::ffi::c_uint = v.offset(LEN1 as isize);\n    (*keep).p = t;\n    check(t, v);",
    ) + "#[repr(C)]\npub struct Keep { pub p: *mut core::ffi::c_uint }\n";
    assert!(code.contains("(*keep).p = t"));
    control(&code, "split");
}

/// X10: `fill`'s `k += 1` under an `if`: `j − k` grows without bound at the loop
/// head, so `j` is unbounded: Unknown, the edge stays. (Report 218's wording put
/// the `if` on `j`; there `j ≤ k ≤ n − 1` still holds and the extent is sound
/// and bounded, so the control is the counter that bounds, not the index.)
#[test]
fn e5c_w267_x10_conditional_counter_is_unknown() {
    let code = X1
        .replace(
            "unsafe extern \"C\" fn fill(mut out: *mut core::ffi::c_uint, n: core::ffi::c_int) {",
            "unsafe extern \"C\" fn fill(mut out: *mut core::ffi::c_uint, n: core::ffi::c_int, c: core::ffi::c_int) {",
        )
        .replace(
            "        j += 1;\n        k += 1;\n",
            "        j += 1;\n        if c != 0 {\n            k += 1;\n        }\n",
        )
        .replace("fill(tail, LEN2);", "fill(tail, LEN2, 1);");
    assert!(code.contains("if c != 0 {\n            k += 1;"));
    control(&code, "split");
}

/// X11: `fill` also writes `out[-1]`: `[124, 140)` meets `[0, 128)`, the lower
/// bound is checked, the edge stays.
#[test]
fn e5c_w267_x11_negative_reach_meets() {
    let code = X1.replace(
        "    k = 0 as core::ffi::c_int;\n",
        "    k = 0 as core::ffi::c_int;\n    *out.offset(-1 as isize) = 0 as core::ffi::c_uint;\n",
    );
    assert!(code.contains("out.offset(-1 as isize)"));
    control(&code, "split");
}

/// X12 (R2): a pointer loaded from memory is Unknown as a base: the edge stays.
#[test]
fn e5c_w267_x12_a_loaded_pointer_is_no_base() {
    let code = X1.replace(
        "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint) {\n    check(v.offset(LEN1 as isize), v);",
        "pub unsafe extern \"C\" fn split(mut h: *mut Holder) {\n    let mut v: *mut core::ffi::c_uint = (*h).p;\n    check(v.offset(LEN1 as isize), v);",
    ) + "#[repr(C)]\npub struct Holder { pub p: *mut core::ffi::c_uint }\n";
    assert!(code.contains("(*h).p"));
    control(&code, "split");
}

/// X13 (R1): `keep` stores its formal into a global, and the caller reads
/// through the global afterwards: `keep`'s extent is Unknown, the edge stays.
#[test]
fn e5c_w267_x13_a_formal_stored_into_a_global_escapes() {
    let code = X1
        .replace("fill(tail, LEN2);", "keep(tail, LEN2);")
        .replace(
            "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint) {\n    check(v.offset(LEN1 as isize), v);",
            "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint) {\n    check(v.offset(LEN1 as isize), v);\n    *G = 1 as core::ffi::c_uint;",
        )
        + "pub static mut G: *mut core::ffi::c_uint = 0 as *mut core::ffi::c_uint;\n\
           unsafe extern \"C\" fn keep(mut t: *mut core::ffi::c_uint, n: core::ffi::c_int) {\n    \
           G = t;\n    *t = 0 as core::ffi::c_uint;\n}\n";
    assert!(code.contains("keep(tail, LEN2)") && code.contains("G = t;"));
    control(&code, "split");
}

/// X14: a pointer read out of the base reaches memory the base's ranges do not
/// describe: `twice` reads `(*x).p` and writes through it, `(*y).data` is a
/// disjoint field, and still the edge stays. (`s.offset(0)`, as in X1, so the
/// issuer reaches the call through a derivation: a copy handed to the call
/// directly is the argument-order rule's.)
#[test]
fn e5c_w267_x14_a_pointer_read_out_of_the_base_ends_the_footprint() {
    const CODE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables)]
#[repr(C)]
pub struct Two {
    pub p: *mut u32,
    pub data: [u32; 4],
}
unsafe extern "C" fn twice(mut x: *mut Two, mut y: *mut Two) {
    *(*x).p = 1;
    (*y).data[0] = 2;
}
#[no_mangle]
pub unsafe extern "C" fn pair(mut s: *mut Two) {
    twice(s.offset(0), s);
}
"#;
    control(CODE, "pair");
}

/// R3: a copy-lend loan over the same disjoint ranges keeps its edge: X1 with
/// `v` the Owning lender of a mutable copy-lend to its first copy.
#[test]
fn e5c_w267_r3_a_copy_lend_loan_is_never_discharged() {
    with_program(X1, |program| {
        let slots = CrateSlots::build(program);
        let split = function(program, "split");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(split)
            .borrow();
        let v = Local::from_u32(1);
        let copy = copies_of(&body, v)[0];
        let slot = |local: Local| {
            SlotRef::Local(
                split,
                slots.fn_local_slots[&split]
                    .slot_for_local_depth(local, 0)
                    .expect("a depth-0 slot"),
            )
        };
        let model = model(program, &slots, "split", &[v]);
        let mut pair = CopyLendPair::new(slot(copy), slot(v));
        pair.mutable = true;
        let lends: FxHashSet<CopyLendPair> = [pair].into_iter().collect();
        let flows = super::origin_flow::analyze_program_origin_flow(program);
        let inventory = std::sync::Arc::new(source_events::collect(program));
        let _ = index_ranges::take_receipts();
        let accepted = source_events::with_inventory(&inventory, || {
            borrow_verify::model_accepts_with_flows_and_copy_lends(
                program, &slots, &flows, &model, true, &lends,
            )
        });
        assert!(!accepted, "a copy-lend loan keeps its edge");
        assert!(
            index_ranges::take_receipts()
                .iter()
                .all(|receipt| receipt.issuer != copy),
            "no receipt discharges the copy-lend loan"
        );
    });
}

/// R3's companion: the same model without the lend (`v` still `Owning`, its
/// first copy an ordinary loan) is accepted, the copy's loan discharged.
#[test]
fn e5c_w267_r3b_the_same_model_without_the_lend_is_accepted() {
    with_program(X1, |program| {
        let slots = CrateSlots::build(program);
        let split = function(program, "split");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(split)
            .borrow();
        let v = Local::from_u32(1);
        let copy = copies_of(&body, v)[0];
        let model = model(program, &slots, "split", &[v]);
        let flows = super::origin_flow::analyze_program_origin_flow(program);
        let inventory = std::sync::Arc::new(source_events::collect(program));
        let _ = index_ranges::take_receipts();
        let accepted = source_events::with_inventory(&inventory, || {
            borrow_verify::model_accepts_with_flows_and_copy_lends(
                program,
                &slots,
                &flows,
                &model,
                true,
                &FxHashSet::default(),
            )
        });
        assert!(accepted, "without the lend the model is accepted");
        assert!(
            index_ranges::take_receipts()
                .iter()
                .any(|receipt| receipt.issuer == copy),
            "the copy's ordinary loan is discharged"
        );
    });
}

/// X15 (the review's M2): `n as isize` used other than as an `offset` count is
/// not assumed to keep its value (`(ssize_t)n` is implementation-defined in
/// C, not UB): the extent is Unknown, the edge stays.
#[test]
fn e5c_w267_x15_usize_as_isize_outside_an_offset_is_unknown() {
    let code = X1
        .replace(
            "unsafe extern \"C\" fn fill(mut out: *mut core::ffi::c_uint, n: core::ffi::c_int) {",
            "unsafe extern \"C\" fn fill(mut out: *mut core::ffi::c_uint, n: usize) {\n    let mut q: isize = n as isize;\n    if q > 2 {\n        return;\n    }\n    *out.offset(q) = 7 as core::ffi::c_uint;\n}\nunsafe extern \"C\" fn unused_fill(mut out: *mut core::ffi::c_uint, n: core::ffi::c_int) {",
        )
        .replace("fill(tail, LEN2);", "fill(tail, 3 as usize);");
    assert!(code.contains("n as isize") && code.contains("fill(tail, 3 as usize)"));
    control(&code, "split");
}

/// X16 (the review's B1): a condition on a boolean whose address is taken
/// goes stale when a callee writes it; none is kept, so `i`'s lower bound is
/// unknown and the edge stays.
#[test]
fn e5c_w267_x16_a_condition_on_an_addressed_boolean_is_dropped() {
    let code = X1
        .replace(
            "unsafe extern \"C\" fn fill(mut out: *mut core::ffi::c_uint, n: core::ffi::c_int) {",
            "unsafe extern \"C\" fn set(mut b: *mut bool) {\n    *b = true;\n}\nunsafe extern \"C\" fn fill(mut out: *mut core::ffi::c_uint, i: isize) {\n    let mut ok: bool = i >= 0;\n    set(&mut ok);\n    if ok && i < 3 {\n        *out.offset(i) = 0 as core::ffi::c_uint;\n    }\n}\nunsafe extern \"C\" fn unused_fill(mut out: *mut core::ffi::c_uint, n: core::ffi::c_int) {",
        )
        .replace("fill(tail, LEN2);", "fill(tail, -1);");
    assert!(code.contains("set(&mut ok)") && code.contains("fill(tail, -1)"));
    control(&code, "split");
}

/// X17: a write through another copy of the base while the view is live is a
/// routed write; it reaches `[0, 4)` against the view's `[128, 140)`, so it is
/// discharged too.
#[test]
fn e5c_w267_x17_a_routed_write_is_discharged() {
    let code = X1.replace(
        "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint) {\n    check(v.offset(LEN1 as isize), v);",
        "pub unsafe extern \"C\" fn split(mut v: *mut core::ffi::c_uint) {\n    let mut t: *mut core::ffi::c_uint = v.offset(LEN1 as isize);\n    let mut w: *mut core::ffi::c_uint = v;\n    *w = 9 as core::ffi::c_uint;\n    fill(t, LEN2);",
    );
    assert!(code.contains("*w = 9"));
    assert_eq!(edges(&code, "split"), 0);
    let (accepted, receipts) = accepts(&code, "split");
    assert!(accepted);
    with_program(&code, |program| {
        let split = function(program, "split");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(split)
            .borrow();
        let write = body
            .basic_blocks
            .iter_enumerated()
            .flat_map(|(block, data)| {
                data.statements.iter().enumerate().filter_map(
                    move |(statement_index, statement)| {
                        let (place, _) = statement.kind.as_assign()?;
                        (place.projection.first() == Some(&rustc_middle::mir::PlaceElem::Deref))
                            .then_some(rustc_middle::mir::Location {
                                block,
                                statement_index,
                            })
                    },
                )
            })
            .next()
            .expect("the write through `w`");
        assert!(
            receipts.iter().any(|receipt| receipt.access == write
                && receipt.loan_bytes == Some((128, 140))
                && receipt.access_bytes == Some((0, 4))
                && receipt.access_writes),
            "the routed write's receipt: {receipts:?}"
        );
    });
}

/// The blake `*_update` shape: `compress(s, (*s).buf.as_ptr())`, with `compress`
/// touching `h` / `t` of `*s` and reading `block` at constant offsets.
const S1: &str = r#"
#![allow(dead_code, unused_mut, unused_variables)]
#[repr(C)]
pub struct State {
    pub h: [u32; 8],
    pub t: [u32; 2],
    pub buf: [u8; 64],
}
unsafe extern "C" fn compress(mut s: *mut State, mut block: *const u8) {
    (*s).h[0] = *block.offset(3) as u32;
    (*s).t[1] = (*s).h[2];
}
#[no_mangle]
pub unsafe extern "C" fn update(mut s: *mut State) {
    compress(s, ((*s).buf).as_ptr());
}
"#;

/// S1: `compress` reaches `[0, 40)` of `*s` through `s` and `buf`'s `[43, 44)`
/// through `block`: disjoint, the edge is gone.
#[test]
fn e5c_w267_s1_struct_fields_disjoint() {
    assert_eq!(edges(S1, "update"), 0);
    let (accepted, receipts) = accepts(S1, "update");
    assert!(accepted);
    assert!(has_receipt(&receipts, (0, 40), (43, 44)));
}

/// S2: `compress` also writes `buf[3]` through `s`: the ranges meet, the edge
/// stays.
#[test]
fn e5c_w267_s2_struct_fields_meet() {
    let code = S1.replace(
        "    (*s).t[1] = (*s).h[2];\n",
        "    (*s).t[1] = (*s).h[2];\n    (*s).buf[3] = 0;\n",
    );
    assert!(code.contains("(*s).buf[3] = 0"));
    control(&code, "update");
}

// ---------------------------------------------------------------------------
// Stage 2 (relay era-5c/267 §3): the field path (E1) and the equality exit
// (E2), β's shape (005's `SPX_merkle_sign` / `SPX_wots_treehashx1` /
// `SPX_wots_gen_leafx1`).
// ---------------------------------------------------------------------------

/// The equality-exit loop: `tree` copies 16 bytes to `auth[h·16 ..]` for every
/// `h` before `h == tree_height` (`wrapping_mul`, `wrapping_add`, as C2Rust
/// writes them); `first` writes `p[3]`.
const B2: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_upper_case_globals)]
pub const SPX_N: core::ffi::c_int = 16 as core::ffi::c_int;
pub const SPX_TREE_HEIGHT: core::ffi::c_int = 66 as core::ffi::c_int / 22 as core::ffi::c_int;
unsafe extern "C" {
    fn memcpy(
        dest: *mut core::ffi::c_void,
        src: *const core::ffi::c_void,
        n: core::ffi::c_ulong,
    ) -> *mut core::ffi::c_void;
}
unsafe extern "C" fn tree(mut auth: *mut u8, mut leaf: *const u8, tree_height: u32) {
    let mut h: u32 = 0;
    h = 0 as u32;
    loop {
        if h == tree_height {
            return;
        }
        memcpy(
            &mut *auth.offset(h.wrapping_mul(SPX_N as u32) as isize) as *mut u8
                as *mut core::ffi::c_void,
            leaf as *const core::ffi::c_void,
            SPX_N as core::ffi::c_ulong,
        );
        h = h.wrapping_add(1);
    }
}
unsafe extern "C" fn first(mut p: *mut u8) {
    *p.offset(3) = 1 as u8;
}
#[no_mangle]
pub unsafe extern "C" fn sign(mut sig: *mut u8, mut leaf: *const u8) {
    let mut auth: *mut u8 = sig.offset(560 as isize);
    first(sig);
    tree(auth, leaf, SPX_TREE_HEIGHT as u32);
}
"#;

/// B2 (E2): `h ≤ tree_height` is inductive once the `h ≠ tree_height` edge
/// reads `h ≤ tree_height − 1`, so `Ext(tree, auth)` is `[0, 16·tree_height)`
/// and the call's is `[560, 608)` against `first`'s `[3, 4)`: the edge is gone.
#[test]
fn e5c_w267_b2_equality_exit_counter() {
    assert_eq!(edges(B2, "sign"), 0, "the disjoint pair leaves no edge");
    let (accepted, receipts) = accepts(B2, "sign");
    assert!(accepted, "`sign`'s pointers are Ref");
    assert!(
        has_receipt(&receipts, (560, 608), (3, 4)),
        "the receipt: the loan's [560, 608), the access's [3, 4): {receipts:?}"
    );
}

/// B2's control: a step of 2 can pass `tree_height` without meeting it, so
/// `h ≤ tree_height` is not inductive and `h` is unbounded: the edge stays.
#[test]
fn e5c_w267_b2b_a_step_that_skips_the_exit_is_unknown() {
    let code = B2.replace("h = h.wrapping_add(1);", "h = h.wrapping_add(2);");
    assert!(code.contains("h.wrapping_add(2)"));
    control(&code, "sign");
}

/// `Ext(tree, auth)` is `[0, 16·tree_height)` written: the exit's counter and
/// the product's range in the formal (`wrapping_mul` by 16 of `h ≤ n − 1`).
#[test]
fn e5c_w267_d5_the_exit_counter_bounds_the_extent_by_the_formal() {
    with_program(B2, |program| {
        let table = IndexRanges::build(program);
        let tree = function(program, "tree");
        assert_eq!(
            bytes(&table.ext(tree, 0)),
            Some((
                Bound::constant(0),
                Bound {
                    formal: Some(2),
                    coef: 16,
                    add: 0
                },
                true
            ))
        );
    });
}

/// β: `sign` stores `sig` into `info.sig` and hands `&mut info` to `tree`,
/// which hands it on to `gen_leaf`; `gen_leaf` copies 16 bytes to
/// `(*info).sig[i·16 ..]` for `i < 35`, reads `(*info).steps[i]` and writes
/// `(*info).addr` through `set_addr`; `tree` copies to `auth[h·16 ..]` for
/// `h < tree_height`.
const B1: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_upper_case_globals)]
pub const SPX_N: core::ffi::c_int = 16 as core::ffi::c_int;
pub const SPX_WOTS_LEN: core::ffi::c_int = 35 as core::ffi::c_int;
pub const SPX_WOTS_BYTES: core::ffi::c_int = SPX_WOTS_LEN * SPX_N;
pub const SPX_TREE_HEIGHT: core::ffi::c_int = 66 as core::ffi::c_int / 22 as core::ffi::c_int;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Info {
    pub sig: *mut u8,
    pub leaf: u32,
    pub steps: *mut u32,
    pub addr: [u32; 8],
}
unsafe extern "C" {
    fn memcpy(
        dest: *mut core::ffi::c_void,
        src: *const core::ffi::c_void,
        n: core::ffi::c_ulong,
    ) -> *mut core::ffi::c_void;
}
unsafe extern "C" fn set_addr(mut addr: *mut u32, mut v: u32) {
    *addr.offset(3) = v;
}
unsafe extern "C" fn gen_leaf(mut dest: *mut u8, mut v_info: *mut core::ffi::c_void) {
    let mut info: *mut Info = v_info as *mut Info;
    let mut buf: [u8; 16] = [0; 16];
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    i = 0 as u32;
    while i < SPX_WOTS_LEN as u32 {
        s = s.wrapping_add(*((*info).steps).offset(i as isize));
        set_addr(((*info).addr).as_mut_ptr(), i);
        memcpy(
            ((*info).sig).offset(i.wrapping_mul(SPX_N as u32) as isize) as *mut core::ffi::c_void,
            buf.as_mut_ptr() as *const core::ffi::c_void,
            SPX_N as core::ffi::c_ulong,
        );
        i = i.wrapping_add(1);
    }
}
unsafe extern "C" fn tree(mut auth: *mut u8, tree_height: u32, mut info: *mut Info) {
    let mut leaf: [u8; 16] = [0; 16];
    gen_leaf(leaf.as_mut_ptr(), info as *mut core::ffi::c_void);
    let mut h: u32 = 0;
    h = 0 as u32;
    loop {
        if h == tree_height {
            return;
        }
        memcpy(
            &mut *auth.offset(h.wrapping_mul(SPX_N as u32) as isize) as *mut u8
                as *mut core::ffi::c_void,
            leaf.as_mut_ptr() as *const core::ffi::c_void,
            SPX_N as core::ffi::c_ulong,
        );
        h = h.wrapping_add(1);
    }
}
#[no_mangle]
pub unsafe extern "C" fn sign(mut sig: *mut u8) {
    let mut auth: *mut u8 = sig.offset(SPX_WOTS_BYTES as isize);
    let mut init: Info = Info {
        sig: 0 as *mut u8,
        leaf: 0 as u32,
        steps: 0 as *mut u32,
        addr: [0; 8],
    };
    let mut info: Info = init;
    let mut steps: [u32; 35] = [0; 35];
    info.sig = sig as *mut u8;
    info.steps = steps.as_mut_ptr();
    set_addr((info.addr).as_mut_ptr(), 1 as u32);
    info.leaf = 7 as u32;
    tree(auth, SPX_TREE_HEIGHT as u32, &mut info);
}
"#;

/// B1 (E1 + E2): `info.sig`'s path reaches `sig + [0, 560)` (written, in
/// `gen_leaf`) and `auth` reaches `sig + [560, 608)` (in `tree`): the edge is
/// gone, `sign`'s pointers are `Ref`, and the receipt names both ranges.
#[test]
fn e5c_w267_b1_field_path_extent() {
    assert_eq!(edges(B1, "sign"), 0, "the disjoint pair leaves no edge");
    let (accepted, receipts) = accepts(B1, "sign");
    assert!(accepted, "`sign`'s pointers are Ref");
    assert!(
        has_receipt(&receipts, (560, 608), (0, 560)),
        "the receipt: the loan's [560, 608), the access's [0, 560): {receipts:?}"
    );
}

/// B1's control (the relay's condition): `gen_leaf` stores to `(*info).sig`:
/// the field path is Unknown, the edge stays.
#[test]
fn e5c_w267_b1b_a_callee_storing_to_the_field_is_unknown() {
    let code = B1.replace(
        "        i = i.wrapping_add(1);\n    }\n}",
        "        i = i.wrapping_add(1);\n    }\n    (*info).sig = dest;\n}",
    );
    assert!(code.contains("(*info).sig = dest;"));
    control(&code, "sign");
}

/// B1's control: `gen_leaf` keeps the loaded field in a global: the loaded
/// value escapes, the edge stays.
#[test]
fn e5c_w267_b1c_a_loaded_field_that_escapes_is_unknown() {
    let code = B1.replace(
        "        i = i.wrapping_add(1);\n    }\n}",
        "        i = i.wrapping_add(1);\n    }\n    G = (*info).sig;\n}\npub static mut G: *mut u8 = 0 as *mut u8;",
    );
    assert!(code.contains("G = (*info).sig;"));
    control(&code, "sign");
}

/// B1's control: `sign` copies the whole holder (the pointer with it) before
/// the call: Unknown, the edge stays.
#[test]
fn e5c_w267_b1d_a_holder_copied_whole_is_unknown() {
    let code = B1.replace(
        "    tree(auth, SPX_TREE_HEIGHT as u32, &mut info);",
        "    let mut other: Info = info;\n    tree(auth, SPX_TREE_HEIGHT as u32, &mut other);",
    );
    assert!(code.contains("let mut other: Info = info;"));
    control(&code, "sign");
}

/// B1's control: `info.steps` points into `sig` too, at 600: `gen_leaf`'s reads
/// of `steps[i]` reach `sig + [600, 740)` (the second field's own path), which
/// meets `auth`'s `[560, 608)`: that pair keeps its edge and `sign` is not
/// accepted. (Its pairs with `info.sig`'s `[0, 560)` are disjoint and
/// discharged, so not `control`.)
#[test]
fn e5c_w267_b1e_a_second_field_into_the_base_meets() {
    let code = B1.replace(
        "    info.steps = steps.as_mut_ptr();",
        "    info.steps = sig.offset(600 as isize) as *mut u32;",
    );
    assert!(code.contains("info.steps = sig.offset(600"));
    assert!(edges(&code, "sign") > 0, "the meeting pair's edge is there");
    let (accepted, receipts) = accepts(&code, "sign");
    assert!(!accepted, "`sign` is not accepted");
    assert!(
        has_receipt(&receipts, (600, 740), (0, 560)),
        "the second field's path is measured: {receipts:?}"
    );
    assert!(
        !receipts.iter().any(|receipt| matches!(
            (receipt.loan_bytes, receipt.access_bytes),
            (Some((600, 740)), Some((560, 608))) | (Some((560, 608)), Some((600, 740)))
        )),
        "the meeting pair is never discharged: {receipts:?}"
    );
}

/// The review's blocker: `info` carries `sig`, a loan is issued after the
/// store, and one call is handed both `sig` and `&info`.
const B1F: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Info {
    pub sig: *mut u8,
    pub leaf: u32,
}
unsafe extern "C" fn first(mut p: *mut u8, mut info: *mut Info) {
    *p.offset(3) = 1 as u8;
    *((*info).sig).offset(100) = 2 as u8;
}
#[no_mangle]
pub unsafe extern "C" fn sign(mut sig: *mut u8) {
    let mut info: Info = Info {
        sig: 0 as *mut u8,
        leaf: 0 as u32,
    };
    info.sig = sig;
    let mut lo: *mut u8 = sig.offset(100 as isize);
    first(sig, &mut info);
    *lo = 1 as u8;
}
"#;

/// B1f (the review's blocker): `first` writes `sig[3]` through its first
/// formal and `sig[100]` through `(*info).sig`; the engine sees the second
/// route only as `&info`, so the access of `sig` at the call carries the
/// holder's path, `[100, 101)` meets `lo`'s, and the edge stays.
#[test]
fn e5c_w267_b1f_a_holder_handed_beside_the_base_carries_its_path() {
    assert!(edges(B1F, "sign") > 0, "the edge is there");
    let (accepted, receipts) = accepts(B1F, "sign");
    assert!(!accepted, "`sign` is not accepted");
    with_program(B1F, |program| {
        let sign = function(program, "sign");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(sign)
            .borrow();
        // `sig`'s copies: the stored one, `lo`'s, the argument.
        let copies = copies_of(&body, Local::from_u32(1));
        assert_eq!(copies.len(), 3, "{copies:?}");
        assert!(
            receipts.iter().all(|receipt| receipt.issuer != copies[1]),
            "`lo`'s loan is never discharged: {receipts:?}"
        );
    });
}

/// B1g: `gen_leaf` writes the whole `*info`: the field's bytes are written,
/// Unknown, the edge stays.
#[test]
fn e5c_w267_b1g_a_callee_writing_the_whole_holder_is_unknown() {
    let code = B1.replace(
        "        i = i.wrapping_add(1);\n    }\n}",
        "        i = i.wrapping_add(1);\n    }\n    *info = Info {\n        sig: 0 as *mut u8,\n        leaf: 0 as u32,\n        steps: 0 as *mut u32,\n        addr: [0; 8],\n    };\n}",
    );
    assert!(code.contains("    *info = Info {"));
    control(&code, "sign");
}

/// B1h: `gen_leaf` copies the field's bytes out (`memcpy` from `info`): Unknown,
/// the edge stays.
#[test]
fn e5c_w267_b1h_a_copy_of_the_field_bytes_is_unknown() {
    let code = B1.replace(
        "        i = i.wrapping_add(1);\n    }\n}",
        "        i = i.wrapping_add(1);\n    }\n    memcpy(dest as *mut core::ffi::c_void, info as *const core::ffi::c_void, 8 as core::ffi::c_ulong);\n}",
    );
    assert!(code.contains("info as *const core::ffi::c_void, 8"));
    control(&code, "sign");
}

/// B1i: `&mut info.sig` handed to a callee that writes through it: Unknown,
/// the edge stays.
#[test]
fn e5c_w267_b1i_the_field_address_written_by_a_callee_is_unknown() {
    let code = B1.replace(
        "    info.leaf = 7 as u32;",
        "    info.leaf = 7 as u32;\n    reset(&mut info.sig);",
    ) + "unsafe extern \"C\" fn reset(mut p: *mut *mut u8) {\n    *p = 0 as *mut u8;\n}\n";
    assert!(code.contains("reset(&mut info.sig);"));
    control(&code, "sign");
}

/// B1j: the holder's address kept in a global: Unknown, the edge stays.
#[test]
fn e5c_w267_b1j_a_holder_address_kept_in_a_global_is_unknown() {
    let code = B1.replace(
        "    info.leaf = 7 as u32;",
        "    info.leaf = 7 as u32;\n    KEPT = &mut info;",
    ) + "pub static mut KEPT: *mut Info = 0 as *mut Info;\n";
    assert!(code.contains("KEPT = &mut info;"));
    control(&code, "sign");
}

/// B1k: the value stored at an offset that is a formal: its reach is not
/// constant, the edge stays.
#[test]
fn e5c_w267_b1k_a_stored_value_at_a_formal_offset_is_unknown() {
    let code = B1
        .replace(
            "pub unsafe extern \"C\" fn sign(mut sig: *mut u8) {",
            "pub unsafe extern \"C\" fn sign(mut sig: *mut u8, k: isize) {",
        )
        .replace(
            "    info.sig = sig as *mut u8;",
            "    info.sig = sig.offset(k);",
        );
    assert!(code.contains("info.sig = sig.offset(k);"));
    control(&code, "sign");
}

// ---------------------------------------------------------------------------
// The domain.
// ---------------------------------------------------------------------------

fn bytes(fp: &Footprint) -> Option<(Bound, Bound, bool)> {
    match fp {
        Footprint::Bytes(bytes) => Some((bytes.lo, bytes.hi, bytes.writes)),
        _ => None,
    }
}

/// `fill`'s index is bounded by its companion counter: `Ext(fill, out)` is
/// `[0, 4·n)` written, affine in `n`.
#[test]
fn e5c_w267_d1_co_incremented_counters_bound_the_index_by_the_formal() {
    with_program(X1, |program| {
        let table = IndexRanges::build(program);
        let fill = function(program, "fill");
        assert_eq!(
            bytes(&table.ext(fill, 0)),
            Some((
                Bound::constant(0),
                Bound {
                    formal: Some(1),
                    coef: 4,
                    add: 0
                },
                true
            ))
        );
    });
}

/// `check`'s `head` is read over `[0, 128)` (an unsigned `wrapping_add` below a
/// `const` item's bound), and `tail` over `fill`'s extent at `n = 3`.
#[test]
fn e5c_w267_d2_wrapping_add_and_const_items_and_instantiation() {
    with_program(X1, |program| {
        let table = IndexRanges::build(program);
        let check = function(program, "check");
        let fill = function(program, "fill");
        assert_eq!(
            bytes(&table.ext(check, 1)),
            Some((Bound::constant(0), Bound::constant(128), false))
        );
        let tail = table.ext(check, 0);
        assert_eq!(
            bytes(&tail),
            Some((Bound::constant(0), Bound::constant(12), true))
        );
        let Footprint::Bytes(tail) = tail else { unreachable!() };
        assert!(tail.summaries.contains(&(fill, 0)));
    });
}

/// The product's range: an unsigned `wrapping_mul` by 16 of `i ≤ 34` reaches
/// `[0, 560)`; a signed one may wrap (defined, no premise), so it is Unknown.
#[test]
fn e5c_w267_d6_an_unsigned_product_is_bounded_a_signed_wrapping_one_is_not() {
    const CODE: &str = r#"
#![allow(dead_code, unused_mut)]
unsafe extern "C" fn put_u(mut p: *mut u8, i: u32) {
    if i < 35 as u32 {
        *p.offset(i.wrapping_mul(16 as u32) as isize) = 0 as u8;
    }
}
unsafe extern "C" fn put_i(mut p: *mut u8, i: i32) {
    if i >= 0 as i32 && i < 35 as i32 {
        *p.offset(i.wrapping_mul(16 as i32) as isize) = 0 as u8;
    }
}
"#;
    with_program(CODE, |program| {
        let table = IndexRanges::build(program);
        assert_eq!(
            bytes(&table.ext(function(program, "put_u"), 0)),
            Some((Bound::constant(0), Bound::constant(545), true))
        );
        assert!(matches!(
            table.ext(function(program, "put_i"), 0),
            Footprint::Unknown(_)
        ));
    });
}

/// An outer counter keeps the bound its test gives it inside an inner loop
/// (005's `SPX_wots_gen_leafx1`, `i` under the `k` loop): only what a loop
/// assigns widens at its head, so `Ext(put, p)` is `[0, 545)`.
#[test]
fn e5c_w267_d7_an_outer_counter_keeps_its_bound_in_an_inner_loop() {
    const CODE: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments)]
unsafe extern "C" fn put(mut p: *mut u8, n: u32) {
    let mut i: u32 = 0;
    let mut k: u32 = 0;
    i = 0 as u32;
    while i < 35 as u32 {
        k = 0 as u32;
        while k < n {
            *p.offset(i.wrapping_mul(16 as u32) as isize) = 0 as u8;
            k = k.wrapping_add(1);
        }
        i = i.wrapping_add(1);
    }
}
"#;
    with_program(CODE, |program| {
        let table = IndexRanges::build(program);
        assert_eq!(
            bytes(&table.ext(function(program, "put"), 0)),
            Some((Bound::constant(0), Bound::constant(545), true))
        );
    });
}

/// A formal the callee returns has no extent this rung (R1).
#[test]
fn e5c_w267_d3_a_returned_formal_is_unknown() {
    const CODE: &str = r#"
#![allow(dead_code, unused_mut)]
unsafe extern "C" fn pass(mut p: *mut u32) -> *mut u32 {
    *p = 1;
    p
}
"#;
    with_program(CODE, |program| {
        let table = IndexRanges::build(program);
        let pass = function(program, "pass");
        assert!(matches!(table.ext(pass, 0), Footprint::Unknown(_)));
    });
}

/// The bound arithmetic: a constant joins any bound, one formal joins itself,
/// two formals do not; a hull compares only like bounds.
#[test]
fn e5c_w267_d4_bounds() {
    let n = Bound {
        formal: Some(0),
        coef: 4,
        add: 0,
    };
    let m = Bound {
        formal: Some(1),
        coef: 4,
        add: 0,
    };
    assert_eq!(
        index_ranges::test_plus(n, Bound::constant(8)),
        Some(Bound {
            formal: Some(0),
            coef: 4,
            add: 8
        })
    );
    assert_eq!(index_ranges::test_plus(n, m), None);
    assert_eq!(
        index_ranges::test_plus(
            n,
            Bound {
                formal: Some(0),
                coef: -4,
                add: 2
            }
        ),
        Some(Bound::constant(2))
    );
}
