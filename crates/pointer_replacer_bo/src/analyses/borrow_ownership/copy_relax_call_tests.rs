//! Witnesses of the copy relaxation through a non-retaining call argument
//! (relay era-5c/269 §1, report 222 §2.1, group I). Each fixture runs the full
//! solve under the export scope; the settled kinds are read by name and the
//! `multi-view` rows from the portable export. Every fixture function is
//! `unsafe extern "C"`, as C2Rust's are (`index_ranges_tests`' module doc).

use std::collections::BTreeMap;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{Local, VarDebugInfoContents};
use rustc_span::def_id::LocalDefId;

use super::{
    SlotRef, borrow_engine, construction::solve_bo_overlap_config, crate_slots::CrateSlots, export,
    mutability_facts::MutFacts, origins::compute_origins, param_overlap, portable_export,
    slots::SlotOwner,
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

/// The solve of a fixture: the settled kinds of its named depth-0 locals
/// (`fn::name`), and the `multi-view` family's rows (their fields).
struct Solved {
    kinds: BTreeMap<String, String>,
    multi_view: Vec<serde_json::Value>,
}

fn solve(code: &str) -> Solved {
    with_program(code, |program| {
        let tcx = program.tcx;
        let slots = CrateSlots::build(program);
        let origins = compute_origins(program);
        let mutability = MutFacts::from_program(program);
        let (verified, captured) = export::with_bo_export(|| {
            solve_bo_overlap_config(
                program,
                &slots,
                &origins,
                &mutability,
                param_overlap::OverlapMode::PreciseReplay,
                Some(param_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
            )
        });
        let verified = verified.expect("the fixture solves");
        let mut kinds = BTreeMap::new();
        for (slot, kind) in &verified.model {
            let SlotRef::Local(function, id) = slot else { continue };
            let s = slots.fn_local_slots[function].slot(*id);
            let SlotOwner::Local(local) = s.owner else { unreachable!() };
            if s.depth != 0 {
                continue;
            }
            let body = tcx
                .mir_drops_elaborated_and_const_checked(*function)
                .borrow();
            let Some(name) = body
                .var_debug_info
                .iter()
                .find_map(|info| match info.value {
                    VarDebugInfoContents::Place(place)
                        if place.local == local && place.projection.is_empty() =>
                    {
                        Some(info.name.to_string())
                    }
                    _ => None,
                })
            else {
                continue;
            };
            let key = format!("{}::{name}", tcx.item_name(function.to_def_id()));
            kinds.insert(key, format!("{kind:?}").to_lowercase());
        }
        let encoded = portable_export::collect(program, &slots, &captured)
            .expect("the portable export")
            .canonical_json()
            .expect("canonical json");
        let value: serde_json::Value = serde_json::from_str(&encoded).expect("json");
        let multi_view = value["families"]["multi-view"]["records"]
            .as_array()
            .map(|records| records.iter().map(|r| r["fields"].clone()).collect())
            .unwrap_or_default();
        Solved { kinds, multi_view }
    })
}

fn kind<'a>(solved: &'a Solved, key: &str) -> &'a str {
    solved
        .kinds
        .get(key)
        .map(String::as_str)
        .unwrap_or_else(|| panic!("no {key}: {:#?}", solved.kinds))
}

/// The conflict edges in `name`, every pointer local of `name` a candidate.
fn edges(code: &str, name: &str) -> usize {
    with_program(code, |program| {
        let found: Vec<LocalDefId> = program
            .functions
            .iter()
            .copied()
            .filter(|f| program.tcx.item_name(f.to_def_id()).as_str() == name)
            .collect();
        assert_eq!(found.len(), 1, "exactly one function {name}");
        let target = found[0];
        let candidates: FxHashMap<LocalDefId, FxHashSet<Local>> = program
            .functions
            .iter()
            .map(|&f| {
                let body = program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(f)
                    .borrow();
                let locals = if f == target {
                    body.local_decls
                        .iter_enumerated()
                        .filter(|(local, decl)| local.as_u32() != 0 && decl.ty.is_any_ptr())
                        .map(|(local, _)| local)
                        .collect()
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

/// The `multi-view` rows of `function` (by its path's last segment).
fn multi_views<'a>(solved: &'a Solved, function: &str) -> Vec<&'a serde_json::Value> {
    solved
        .multi_view
        .iter()
        .filter(|row| {
            row["function"]
                .as_str()
                .is_some_and(|f| f.rsplit("::").next() == Some(function))
        })
        .collect()
}

/// The non-retaining callee (SPHINCS+'s `thash`, `haraka512_perm`): `inp` is
/// read into a local buffer, then `out` is written. `__BODY__` takes a
/// variant's extra statements.
const MIX: &str = r#"
unsafe extern "C" fn mix(out: *mut u8, inp: *const u8, n: i32, addr: *mut u32) {
    __BODY__
    let mut buf: [u8; 64] = [0; 64];
    let mut i: i32 = 0;
    while i < n && i < 64 {
        buf[i as usize] = *inp.offset(i as isize);
        i += 1;
    }
    i = 0;
    while i < n && i < 64 {
        *out.offset(i as isize) = buf[i as usize] ^ *addr as u8;
        i += 1;
    }
}
"#;

/// The caller: `work`'s formal lent twice to one call, in place, beside an
/// argument that is itself a call, as 005's `SPX_thash(out, out, 1, ctx,
/// addr.as_mut_ptr())`, the `in` formal `*const`. `__CALL__` is the call.
const WORK: &str = r#"
unsafe extern "C" fn work(out: *mut u8) {
    let mut addr: [u32; 8] = [0; 8];
    *out = 1;
    __CALL__;
    *out = 2;
}
#[no_mangle] pub unsafe extern "C" fn run() -> u8 {
    let mut x: [u8; 64] = [0; 64];
    work(x.as_mut_ptr());
    return x[0];
}
"#;

const IN_PLACE: &str = "mix(out, out, 16, addr.as_mut_ptr())";

/// `mix` with `body` first, and `work` making `call`, after `extra` items.
fn program(extra: &str, body: &str, call: &str) -> String {
    format!(
        "{extra}\n{}\n{}",
        MIX.replace("__BODY__", body),
        WORK.replace("__CALL__", call)
    )
}

/// (a) In place, a non-retaining local callee: the subject is Ref, the edge
/// between its two argument copies is still there, and the call carries a
/// `multi-view` row with k = 2.
#[test]
fn e5c_w269_a_in_place_non_retaining_callee_subject_ref() {
    let code = program("", "", IN_PLACE);
    assert!(
        edges(&code, "work") > 0,
        "the edge between the copies stays"
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "ref", "{:#?}", solved.kinds);
    let rows = multi_views(&solved, "work");
    assert_eq!(rows.len(), 1, "{rows:#?}");
    assert_eq!(rows[0]["subject"], 1, "{rows:#?}");
    assert_eq!(rows[0]["k"], 2, "{rows:#?}");
}

/// (b) A callee that stores its formal into a global retains it: Raw.
#[test]
fn e5c_w269_b_a_callee_storing_into_a_global_keeps_the_subject_raw() {
    let code = program(
        "static mut KEEP: *const u8 = 0 as *const u8;",
        "KEEP = inp;",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
    // The `out` copy is admitted (`mix` never retains `out`), so the call has
    // its row; the `inp` copy is not, and drags the subject Raw: the row is
    // per admission, and its obligation moot while the subject is Raw.
    assert_eq!(multi_views(&solved, "work").len(), 1);
}

/// (b′) A callee that stores its formal into a field through another formal
/// retains it: Raw.
#[test]
fn e5c_w269_b2_a_callee_storing_into_a_field_keeps_the_subject_raw() {
    let code = program(
        "#[repr(C)] pub struct H { pub p: *const u8, pub n: i32 }\n\
         static mut HOLD: H = H { p: 0 as *const u8, n: 0 };",
        "let h: *mut H = &raw mut HOLD; (*h).p = inp;",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
}

/// (c) The formal passed on to a callee that retains it: Raw (transitive).
#[test]
fn e5c_w269_c_a_formal_passed_to_a_retaining_callee_keeps_the_subject_raw() {
    let code = program(
        "static mut KEEP: *const u8 = 0 as *const u8;\n\
         unsafe extern \"C\" fn stash(q: *const u8) { KEEP = q; }",
        "stash(inp);",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
}

/// (c′) The control: the formal passed on to a callee that only reads it
/// (haraka's `br_range_dec32le`): Ref.
#[test]
fn e5c_w269_c2_a_formal_passed_to_a_reading_callee_keeps_the_subject_ref() {
    let code = program(
        "unsafe extern \"C\" fn peek(q: *const u8) -> u8 { return *q; }",
        "*out = peek(inp);",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "ref", "{:#?}", solved.kinds);
}

/// (d) A foreign callee without a contract row: Raw.
#[test]
fn e5c_w269_d_a_foreign_callee_without_a_row_keeps_the_subject_raw() {
    let code = program(
        "unsafe extern \"C\" { fn consume(a: *mut u8, b: *const u8, n: i32, addr: *mut u32); }",
        "",
        "consume(out, out, 16, addr.as_mut_ptr())",
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
}

/// (e) `memmove(p, p + k, n)`: the contract row retains nothing, so the
/// subject is Ref, with a `multi-view` row of k = 2.
#[test]
fn e5c_w269_e_memmove_within_one_buffer_subject_ref() {
    let code = r#"
unsafe extern "C" {
    fn memmove(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: usize) -> *mut core::ffi::c_void;
}
unsafe extern "C" fn shift(arr: *mut u8, k: i32, n: usize) {
    *arr = 1;
    memmove(arr as *mut core::ffi::c_void, arr.offset(k as isize) as *const core::ffi::c_void, n);
    *arr = 2;
}
#[no_mangle] pub unsafe extern "C" fn run() -> u8 {
    let mut x: [u8; 64] = [0; 64];
    shift(x.as_mut_ptr(), 4, 16);
    return x[0];
}
"#;
    let solved = solve(code);
    assert_eq!(kind(&solved, "shift::arr"), "ref", "{:#?}", solved.kinds);
    let rows = multi_views(&solved, "shift");
    assert_eq!(rows.len(), 1, "{rows:#?}");
    assert_eq!(rows[0]["k"], 2, "{rows:#?}");
}

/// (f) A call through a function pointer: Raw.
#[test]
fn e5c_w269_f_a_call_through_a_function_pointer_keeps_the_subject_raw() {
    let code = program(
        "",
        "",
        "let f: unsafe extern \"C\" fn(*mut u8, *const u8, i32, *mut u32) = mix; \
         f(out, out, 16, addr.as_mut_ptr())",
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
}

/// (g) A recursive callee, though it never hands `inp` on: Raw.
#[test]
fn e5c_w269_g_a_recursive_callee_keeps_the_subject_raw() {
    let code = program(
        "",
        "if n > 1 { let mut t: [u8; 64] = [0; 64]; mix(t.as_mut_ptr(), t.as_ptr(), n - 1, addr); }",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
}

/// (h) The 030 shape, `fma_array(out, out, out, out, n)`: Ref in the model,
/// with a `multi-view` row of k = 4. Under Tree Borrows the four views are
/// sound only if they derive from ONE raw pointer (the emission's obligation;
/// `copy_relax`'s module doc).
#[test]
fn e5c_w269_h_four_views_to_one_call_subject_ref_multi_view_four() {
    let code = r#"
unsafe extern "C" fn fma_array(out: *mut f64, a: *const f64, b: *const f64, c: *const f64, n: i32) {
    let mut i: i32 = 0;
    while i < n {
        *out.offset(i as isize) = *a.offset(i as isize) * *b.offset(i as isize) + *c.offset(i as isize);
        i += 1;
    }
}
unsafe extern "C" fn driver(out: *mut f64, n: i32) {
    *out = 1.0;
    fma_array(out, out, out, out, n);
    *out += 1.0;
}
#[no_mangle] pub unsafe extern "C" fn run() -> f64 {
    let mut x: [f64; 8] = [1.0; 8];
    driver(x.as_mut_ptr(), 8);
    return x[0];
}
"#;
    assert!(
        edges(code, "driver") > 0,
        "the edges between the copies stay"
    );
    let solved = solve(code);
    assert_eq!(kind(&solved, "driver::out"), "ref", "{:#?}", solved.kinds);
    let rows = multi_views(&solved, "driver");
    assert_eq!(rows.len(), 1, "{rows:#?}");
    assert_eq!(rows[0]["subject"], 1, "{rows:#?}");
    assert_eq!(rows[0]["k"], 4, "{rows:#?}");
    assert_eq!(
        rows[0]["arguments"],
        serde_json::json!([0, 1, 2, 3]),
        "{rows:#?}"
    );
}

/// (i) The review's blocker: the copy's own storage handed to `memcpy` as
/// its source (`memcpy(&saved, &x, sizeof x)`) carries the copy's value into
/// a global. The subject stays Raw.
#[test]
fn e5c_w269_i_memcpy_out_of_the_copys_own_storage_keeps_the_subject_raw() {
    let code = r#"
unsafe extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: usize) -> *mut core::ffi::c_void;
}
static mut SAVED: *mut u8 = 0 as *mut u8;
unsafe extern "C" fn f(y: *mut u8) {
    let x: *mut u8 = y;
    *y = 1;
    memcpy(
        &raw mut SAVED as *mut core::ffi::c_void,
        &raw const x as *const core::ffi::c_void,
        8,
    );
    *y = 2;
    *SAVED = 3;
}
#[no_mangle] pub unsafe extern "C" fn run() -> u8 {
    let mut b: [u8; 8] = [0; 8];
    f(b.as_mut_ptr());
    return b[0];
}
"#;
    let solved = solve(code);
    assert_eq!(kind(&solved, "f::y"), "raw", "{:#?}", solved.kinds);
}

/// (j) A callee that returns its formal retains it: Raw.
#[test]
fn e5c_w269_j_a_callee_returning_its_formal_keeps_the_subject_raw() {
    let code = program(
        "static mut LAST: *const u8 = 0 as *const u8;\n\
         unsafe extern \"C\" fn pass(q: *const u8) -> *const u8 { return q; }",
        "LAST = pass(inp);",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
}

/// (k) A callee that keeps its formal's address as an integer: Raw.
#[test]
fn e5c_w269_k_a_callee_casting_its_formal_to_an_integer_keeps_the_subject_raw() {
    let code = program(
        "static mut ADDR: usize = 0;",
        "ADDR = inp as usize;",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
}

/// (l) A callee that steps its own formal (haraka's `br_range_dec32le`,
/// `src = src.offset(4)`) is followed through every value the formal holds:
/// only read through, Ref; the stepped value stored into a global, Raw.
#[test]
fn e5c_w269_l_a_callee_stepping_its_formal_is_followed_through_its_values() {
    let stepping = |extra: &str, tail: &str| {
        program(
            extra,
            &format!(
                "let mut k: i32 = 0; while k < n {{ *out = *out ^ *inp; inp = inp.offset(1); k += 1; }}{tail}"
            ),
            IN_PLACE,
        )
        .replace("inp: *const u8, n: i32", "mut inp: *const u8, n: i32")
    };
    let code = stepping("", "");
    assert!(code.contains("mut inp"));
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "ref", "{:#?}", solved.kinds);
    let code = stepping(
        "static mut LAST: *const u8 = 0 as *const u8;",
        " LAST = inp;",
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
}

/// (q) A callee that copies bytes out of its formal (005's `SPX_thash`,
/// `memcpy(buf, in, n)`): the bytes of the pointee carry none of the
/// formal's value, so the subject is Ref.
#[test]
fn e5c_w269_q_a_callee_copying_bytes_out_of_its_formal_keeps_the_subject_ref() {
    let code = program(
        "unsafe extern \"C\" {\n    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, \
         n: usize) -> *mut core::ffi::c_void;\n}",
        "let mut b2: [u8; 64] = [0; 64]; \
         memcpy(b2.as_mut_ptr() as *mut core::ffi::c_void, inp as *const core::ffi::c_void, 16); \
         *out = b2[0];",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "ref", "{:#?}", solved.kinds);
}

/// (s) A callee that takes its formal's address: Raw.
#[test]
fn e5c_w269_s_a_callee_taking_its_formals_address_keeps_the_subject_raw() {
    let code = program(
        "static mut SLOT: *const *const u8 = 0 as *const *const u8;",
        "SLOT = &raw const inp;",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
}

/// (m) A callee in a recursive SCC of two: Raw.
#[test]
fn e5c_w269_m_a_callee_in_a_two_function_cycle_keeps_the_subject_raw() {
    let code = program(
        "unsafe extern \"C\" fn again(n: i32, addr: *mut u32) {\n    \
         let mut t: [u8; 64] = [0; 64];\n    mix(t.as_mut_ptr(), t.as_ptr(), n, addr);\n}",
        "if n > 1 { again(n - 1, addr); }",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
}

/// (n) E1's holder: the formal stored into a local struct handed to a
/// retaining callee is retained (Raw); read back and dropped with the call,
/// it is not (Ref).
#[test]
fn e5c_w269_n_a_holder_handed_to_a_retaining_callee_keeps_the_subject_raw() {
    let holder = "#[repr(C)] pub struct Hd { pub p: *const u8, pub n: i32 }\n\
                  static mut KEEPH: *const u8 = 0 as *const u8;\n\
                  unsafe extern \"C\" fn take(h: *mut Hd) { KEEPH = (*h).p; }";
    let code = program(
        holder,
        "let mut h: Hd = Hd { p: 0 as *const u8, n: 0 }; h.p = inp; take(&mut h);",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "raw", "{:#?}", solved.kinds);
    let code = program(
        holder,
        "let mut h: Hd = Hd { p: 0 as *const u8, n: 0 }; h.p = inp; *out = *h.p;",
        IN_PLACE,
    );
    let solved = solve(&code);
    assert_eq!(kind(&solved, "work::out"), "ref", "{:#?}", solved.kinds);
}

/// (o) `multi-view` counts views of the subject's bytes only: a pointer
/// loaded through a view (`(*x).next`) and the address of the subject's own
/// storage (`&mut y`) are not views, so neither call has a row.
#[test]
fn e5c_w269_o_a_loaded_pointer_or_an_address_of_the_subject_is_no_view() {
    let code = r#"
#[repr(C)] pub struct nd { pub v: u8, pub next: *mut nd }
unsafe extern "C" fn g(a: *mut nd, b: *mut nd, addr: *mut u32) { (*a).v = (*b).v ^ *addr as u8; }
unsafe extern "C" fn h2(pp: *mut *mut nd, b: *mut nd, addr: *mut u32) { (*b).v = (**pp).v ^ *addr as u8; }
unsafe extern "C" fn walk(x: *mut nd) {
    let mut addr: [u32; 8] = [0; 8];
    (*x).v = 1;
    g(x, (*x).next, addr.as_mut_ptr());
    (*x).v = 2;
}
unsafe extern "C" fn twice(mut y: *mut nd) {
    let mut addr: [u32; 8] = [0; 8];
    (*y).v = 1;
    h2(&mut y, y, addr.as_mut_ptr());
    (*y).v = 2;
}
#[no_mangle] pub unsafe extern "C" fn run() -> u8 {
    let mut b = nd { v: 0, next: 0 as *mut nd };
    let mut a = nd { v: 0, next: &mut b };
    walk(&mut a);
    twice(&mut a);
    return a.v;
}
"#;
    let solved = solve(code);
    assert!(
        multi_views(&solved, "walk").is_empty(),
        "{:#?}",
        solved.multi_view
    );
    assert!(
        multi_views(&solved, "twice").is_empty(),
        "{:#?}",
        solved.multi_view
    );
}

/// (p) A reborrow of the subject live across the call, used after it: the
/// callee's write through the admitted view meets it, so the two are never
/// both Ref.
#[test]
fn e5c_w269_p_a_reborrow_live_across_the_call_is_not_ref_beside_the_subject() {
    let code = WORK.replace(
        "    *out = 1;\n    __CALL__;\n    *out = 2;",
        "    let r: *mut u8 = out;\n    *r = 1;\n    __CALL__;\n    *r = 2;",
    );
    assert!(code.contains("*r = 2"));
    let code = format!(
        "{}\n{}",
        MIX.replace("__BODY__", ""),
        code.replace("__CALL__", IN_PLACE)
    );
    let solved = solve(&code);
    assert!(
        kind(&solved, "work::out") != "ref" || kind(&solved, "work::r") != "ref",
        "{:#?}",
        solved.kinds
    );
}
