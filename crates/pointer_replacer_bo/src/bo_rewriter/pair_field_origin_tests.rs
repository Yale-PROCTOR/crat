//! wave-6v witnesses for R579-3: the field-origin route through the certificate
//! layer. Reduced from brotli's encoder: `RingBufferInitBuffer` stores a
//! `BrotliAllocate` local into `(*rb).data_` and `(*rb).data_ + 2` into
//! `(*rb).buffer_`; `EncodeData` reads `(*s).ringbuffer_.buffer_` into a local
//! and hands it beside `&mut (*s).hasher_` / `&mut (*s).params` / `m` to
//! `InitOrStitchToPreviousBlock`, whose callees see only parameters.
//!
//! The three positive witnesses were RED before the rule (the test-only commit
//! that precedes it); every control is a refusal of R579-3's lines 1–7 and has
//! its own deliberate fault (report 047).

use crate::bo_rewriter;

/// The ring-buffer shape. Markers are replaced by each control.
const RING: &str = r#"
    #![allow(dead_code, unused_mut, unused_assignments, unused_variables, non_snake_case)]
    use core::ffi::c_void;
    extern "C" {
        fn malloc(n: u64) -> *mut c_void;
        fn free(p: *mut c_void);
        fn memcpy(d: *mut c_void, s: *const c_void, n: u64) -> *mut c_void;
    }
    #[repr(C)] #[derive(Copy, Clone)] pub struct MemoryManager { pub opaque: *mut c_void }
    #[repr(C)] #[derive(Copy, Clone)] pub struct RingBuffer { pub size_: u32, pub data_: *mut u8, pub buffer_: *mut u8 }
    #[repr(C)] #[derive(Copy, Clone)] pub struct Hasher { pub extra: *mut c_void, pub dict_num: u32 }
    #[repr(C)] #[derive(Copy, Clone)] pub struct Params { pub quality: i32 }
    #[repr(C)] #[derive(Copy, Clone)] pub struct State { pub mm: MemoryManager, pub ringbuffer_: RingBuffer, pub hasher_: Hasher, pub params: Params }
    unsafe fn RingBufferInit(rb: *mut RingBuffer) {
        (*rb).data_ = 0 as *mut u8;
        (*rb).buffer_ = 0 as *mut u8;
    }
    unsafe fn RingBufferInitBuffer(m: *mut MemoryManager, buflen: u32, rb: *mut RingBuffer) {
        let mut new_data = if buflen > 0 { malloc(buflen as u64 + 2) as *mut u8 } else { 0 as *mut u8 };
        if !((*rb).data_).is_null() {
            free((*rb).data_ as *mut c_void);
            (*rb).data_ = 0 as *mut u8;
        }
        (*rb).data_ = new_data;
        (*rb).buffer_ = ((*rb).data_).offset(2 as isize);
    }
    unsafe fn PrepareH2(h: *mut Hasher, data: *const u8) { (*h).dict_num = *data as u32; }
    unsafe fn HasherSetup(m: *mut MemoryManager, hasher: *mut Hasher, params: *mut Params, data: *const u8) {
        (*hasher).dict_num = (*params).quality as u32;
        (*params).quality = 1;
        (*m).opaque = (*hasher).extra;
        PrepareH2(hasher, data);
    }
    unsafe fn InitOrStitch(m: *mut MemoryManager, hasher: *mut Hasher, data: *const u8, params: *mut Params) {
        HasherSetup(m, hasher, params, data);
    }
    unsafe fn EncodeData(s: *mut State) {
        let mut data = 0 as *mut u8;
        data = (*s).ringbuffer_.buffer_;
        InitOrStitch(&mut (*s).mm, &mut (*s).hasher_, data, &mut (*s).params);
    }
    /*EXTRA*/
    pub unsafe fn Create(q: *mut u8) -> *mut State {
        let s = malloc(64) as *mut State;
        RingBufferInit(&mut (*s).ringbuffer_);
        RingBufferInitBuffer(&mut (*s).mm, 16, &mut (*s).ringbuffer_);
        EncodeData(s);
        /*CALLS*/
        s
    }
"#;

fn variant(extra: &str, calls: &str) -> String {
    RING.replace("/*EXTRA*/", extra).replace("/*CALLS*/", calls)
}

/// Every recorded outcome of `(caller → callee, left, right)`, in site order.
fn outcomes(src: &str, caller: &str, callee: &str, left: usize, right: usize) -> Vec<String> {
    let mut found = Vec::new();
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let program = bo_rewriter::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = bo_rewriter::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        for row in index.probe_rows(&program) {
            if tcx.item_name(row.caller.to_def_id()).as_str() == caller
                && tcx.item_name(row.callee.to_def_id()).as_str() == callee
                && (row.left, row.right) == (left, right)
            {
                found.push(format!(
                    "{}|{}|{}",
                    row.outcome, row.left_class, row.right_class
                ));
            }
        }
    })
    .expect("fixture compilation");
    assert!(
        !found.is_empty(),
        "no {caller} -> {callee} {left}/{right} row"
    );
    found
}

fn certified(rows: &[String]) -> bool {
    rows.iter().all(|row| row.starts_with("pair-disjoint:"))
}

fn assert_unproved(rows: &[String], what: &str) {
    assert!(
        rows.iter()
            .all(|row| row.starts_with("pair-disjointness-unproved")),
        "{what}: {rows:?}"
    );
}

// ---------------------------------------------------------------- positives

/// W1. `EncodeData`'s three pairs: `data` is the block `(*s).ringbuffer_`
/// holds, so it is disjoint from every place inside `*s`.
#[test]
fn w6v_encode_data_three_pairs_are_distinct_roots_through_the_ring_buffer() {
    let src = variant("", "");
    for (left, right) in [(0, 2), (1, 2), (2, 3)] {
        let rows = outcomes(&src, "EncodeData", "InitOrStitch", left, right);
        assert!(
            rows.iter()
                .all(|row| row.starts_with("pair-disjoint:distinct-roots|")),
            "{left}/{right}: {rows:?}"
        );
        assert!(
            rows.iter().all(|row| row.contains("fresh-field:buffer_")),
            "the carried local names the field: {rows:?}"
        );
    }
}

/// W2. The callees' own `(hasher, data)` pairs certify by (e), because the
/// only caller chain bottoms out at `EncodeData`'s now-certified pair.
#[test]
fn w6v_hasher_tree_parameter_pairs_certify_through_encode_data() {
    let src = variant("", "");
    for (caller, callee, left, right) in [
        ("InitOrStitch", "HasherSetup", 1, 3),
        ("HasherSetup", "PrepareH2", 0, 1),
    ] {
        let rows = outcomes(&src, caller, callee, left, right);
        assert!(
            rows.iter()
                .all(|row| row.starts_with("pair-disjoint:parameter-pair|")),
            "{caller} -> {callee}: {rows:?}"
        );
    }
}

/// W3 (line 5, `void *` on the same discipline). The same shape with
/// `buffer_` a `*mut c_void` certifies the same way.
#[test]
fn w6v_a_void_pointer_field_is_admitted_on_the_same_discipline() {
    let src = variant("", "")
        .replace("pub buffer_: *mut u8 }", "pub buffer_: *mut c_void }")
        .replace(
            "(*rb).buffer_ = 0 as *mut u8;",
            "(*rb).buffer_ = 0 as *mut c_void;",
        )
        .replace(
            "(*rb).buffer_ = ((*rb).data_).offset(2 as isize);",
            "(*rb).buffer_ = ((*rb).data_).offset(2 as isize) as *mut c_void;",
        )
        .replace(
            "let mut data = 0 as *mut u8;",
            "let mut data = 0 as *mut c_void;",
        )
        .replace(
            "(*s).hasher_, data, &mut",
            "(*s).hasher_, data as *const u8, &mut",
        );
    let rows = outcomes(&src, "EncodeData", "InitOrStitch", 1, 2);
    assert!(certified(&rows), "{rows:?}");
}

// ---------------------------------------------------------------- controls

/// Line 1: a store of a parameter's value into `data_` refuses it, and so
/// `buffer_`, derived from it (the fixpoint). Fault F1: that store admitted.
#[test]
fn w6v_control_a_parameter_value_stored_into_the_field_refuses_it() {
    let src = variant(
        "unsafe fn Retarget(rb: *mut RingBuffer, p: *mut u8) { (*rb).data_ = p; }",
        "Retarget(&mut (*s).ringbuffer_, q);",
    );
    assert_unproved(
        &outcomes(&src, "EncodeData", "InitOrStitch", 1, 2),
        "a parameter's value in data_",
    );
}

/// Line 1: an offset of ANOTHER base's field refuses the field. Fault F1b: the
/// same-base condition of (d) dropped.
#[test]
fn w6v_control_an_offset_from_another_base_refuses_the_field() {
    let src = variant(
        "unsafe fn Share(rb: *mut RingBuffer, other: *mut RingBuffer) { (*rb).buffer_ = ((*other).data_).offset(2 as isize); }",
        "Share(&mut (*s).ringbuffer_, &mut (*s).ringbuffer_);",
    );
    assert_unproved(
        &outcomes(&src, "EncodeData", "InitOrStitch", 1, 2),
        "buffer_ from another base",
    );
}

/// Line 2: (c) with a base that is NOT entry storage — the block stored into
/// a struct that lives inside that very block. Fault F2: the entry-storage
/// condition dropped.
#[test]
fn w6v_control_a_fresh_local_stored_into_its_own_block_refuses_the_field() {
    let src = variant(
        "unsafe fn Fresh() -> *mut RingBuffer { let mut p = malloc(64) as *mut u8; let mut t = p as *mut RingBuffer; (*t).data_ = p; t }",
        "Fresh();",
    );
    assert_unproved(
        &outcomes(&src, "EncodeData", "InitOrStitch", 1, 2),
        "data_ stored through a non-entry base",
    );
}

/// Line 3: a whole-struct copy writes both fields without a field store.
/// Fault F3a: the whole-value arm dropped.
#[test]
fn w6v_control_a_whole_struct_copy_refuses_the_struct() {
    let src = variant(
        "unsafe fn CopyRb(dst: *mut RingBuffer, src: *const RingBuffer) { *dst = *src; }",
        "CopyRb(&mut (*s).ringbuffer_, &mut (*s).ringbuffer_);",
    );
    assert_unproved(
        &outcomes(&src, "EncodeData", "InitOrStitch", 1, 2),
        "a whole RingBuffer copy",
    );
}

/// Line 3: a byte writer aimed at a CONTAINER of the struct. Fault F3b: the
/// byte-writer arm dropped.
#[test]
fn w6v_control_a_byte_writer_at_a_container_refuses_the_struct() {
    let src = variant(
        "unsafe fn CopyState(dst: *mut State, src: *const State) { memcpy(dst as *mut c_void, src as *const c_void, 64); }",
        "CopyState(s, s);",
    );
    assert_unproved(
        &outcomes(&src, "EncodeData", "InitOrStitch", 1, 2),
        "memcpy onto the State",
    );
}

/// Line 4: a pointer reaching the struct retyped to `*mut *mut u8` writes its
/// first pointer field. Fault F4: the cast arm dropped.
#[test]
fn w6v_control_a_punning_cast_refuses_the_struct() {
    let src = variant(
        "unsafe fn Pun(rb: *mut RingBuffer, p: *mut u8) { let q = rb as *mut *mut u8; *q = p; }",
        "Pun(&mut (*s).ringbuffer_, q);",
    );
    assert_unproved(
        &outcomes(&src, "EncodeData", "InitOrStitch", 1, 2),
        "a pun of *mut RingBuffer",
    );
}

/// Line 5: a union is never a key. Fault F5: the union refusal in
/// `data_field_key` dropped.
#[test]
fn w6v_control_a_union_field_is_never_admitted() {
    let src = variant("", "").replace(
        "#[repr(C)] #[derive(Copy, Clone)] pub struct RingBuffer { pub size_: u32, pub data_: *mut u8, pub buffer_: *mut u8 }",
        "#[repr(C)] #[derive(Copy, Clone)] pub union RingBuffer { pub size_: u32, pub data_: *mut u8, pub buffer_: *mut u8 }",
    );
    assert_unproved(
        &outcomes(&src, "EncodeData", "InitOrStitch", 1, 2),
        "a union field",
    );
}

/// Line 6: `data_` and `buffer_` are ONE block; fields admitted through a local
/// or an offset never take the different-fields clause. Fault F6: the
/// same-base-only flag ignored.
#[test]
fn w6v_control_two_offset_related_fields_are_not_separated() {
    let src = variant(
        "unsafe fn TwoViews(a: *mut u8, b: *const u8) { *a = *b; }
         unsafe fn Views(s: *mut State) { TwoViews((*s).ringbuffer_.data_, (*s).ringbuffer_.buffer_); }",
        "Views(s);",
    );
    let rows = outcomes(&src, "Views", "TwoViews", 0, 1);
    assert!(
        rows.iter()
            .all(|row| row.contains("fresh-field:data_") && row.contains("fresh-field:buffer_")),
        "both sides are admitted fields: {rows:?}"
    );
    assert_unproved(&rows, "data_ beside buffer_");
}

/// Line 7: a local fed by the field out of TWO bases has no single root.
/// Fault F7a: the single-read condition dropped.
#[test]
fn w6v_control_a_local_read_from_two_bases_is_not_carried() {
    let src = variant(
        "unsafe fn TwoBases(s: *mut State, t: *mut State, c: i32) {
             let mut d = (*s).ringbuffer_.buffer_;
             if c != 0 { d = (*t).ringbuffer_.buffer_; }
             InitOrStitch(&mut (*s).mm, &mut (*s).hasher_, d, &mut (*s).params);
         }",
        "TwoBases(s, s, 0);",
    );
    assert_unproved(
        &outcomes(&src, "TwoBases", "InitOrStitch", 1, 2),
        "d read out of two bases",
    );
}

/// Line 7: a local whose address is taken is not carried. Fault F7b: the
/// carry's own address-taken check dropped.
#[test]
fn w6v_control_an_address_taken_local_is_not_carried() {
    let src = variant(
        "unsafe fn Poke(p: *mut *mut u8) {}
         unsafe fn Taken(s: *mut State) {
             let mut d = (*s).ringbuffer_.buffer_;
             Poke(&mut d);
             InitOrStitch(&mut (*s).mm, &mut (*s).hasher_, d, &mut (*s).params);
         }",
        "Taken(s);",
    );
    assert_unproved(
        &outcomes(&src, "Taken", "InitOrStitch", 1, 2),
        "an address-taken d",
    );
}

/// Line 7: a parameter assigned from the field is not carried — its entry
/// value is another source. Fault F7c: the `let`-declared condition dropped.
#[test]
fn w6v_control_a_parameter_is_not_carried() {
    let src = variant(
        "unsafe fn Param(s: *mut State, mut d: *mut u8) {
             d = (*s).ringbuffer_.buffer_;
             InitOrStitch(&mut (*s).mm, &mut (*s).hasher_, d, &mut (*s).params);
         }",
        "Param(s, q);",
    );
    assert_unproved(
        &outcomes(&src, "Param", "InitOrStitch", 1, 2),
        "a parameter d",
    );
}

// ------------------------------------------------- R583-5: G1 and G2

/// G1: a byte or `void` cast of a pointer that reaches the struct hands its
/// bytes to code the store scan cannot read, so it counts as a writer. Fault
/// G1-F1: byte and `void` targets exempt again (the pre-G1 rule).
#[test]
fn w6v_control_a_byte_or_void_cast_of_the_struct_refuses_it() {
    for (name, body) in [
        (
            "byte",
            "unsafe fn Bytes(rb: *mut RingBuffer) { let p = rb as *mut u8; *p.offset(8) = 0; }",
        ),
        (
            "void",
            "unsafe fn Bytes(rb: *mut RingBuffer) { let p = rb as *mut c_void; *(p as *mut u64) = 0; }",
        ),
    ] {
        let src = variant(body, "Bytes(&mut (*s).ringbuffer_);");
        assert_unproved(
            &outcomes(&src, "EncodeData", "InitOrStitch", 1, 2),
            &format!("a {name} cast of *mut RingBuffer"),
        );
    }
}

/// G1's exemption: a `void` cast whose value goes STRAIGHT to a deallocator —
/// libc `free`, a contract's free function, or a `free_func` field call — only
/// releases the object. Fault G1-F2: the exemption dropped.
#[test]
fn w6v_a_cast_straight_to_a_deallocator_is_not_a_writer() {
    for (name, body, call) in [
        (
            "free",
            "unsafe fn Release(s: *mut State) { free(s as *mut c_void); }",
            "Release(s);",
        ),
        (
            "free_func field",
            "#[repr(C)] pub struct Freer { pub free_func: Option<unsafe extern \"C\" fn(*mut c_void, *mut c_void)>, pub opaque: *mut c_void }
             unsafe fn Release(f: *mut Freer, s: *mut State) { ((*f).free_func).expect(\"non-null function pointer\")((*f).opaque, s as *mut c_void); }",
            "Release(0 as *mut Freer, s);",
        ),
        (
            "free_func local",
            "#[repr(C)] pub struct Freer { pub free_func: Option<unsafe extern \"C\" fn(*mut c_void, *mut c_void)>, pub opaque: *mut c_void }
             unsafe fn Release(f: *mut Freer, s: *mut State) { let mut free_func = (*f).free_func; free_func.expect(\"non-null function pointer\")((*f).opaque, s as *mut c_void); }",
            "Release(0 as *mut Freer, s);",
        ),
    ] {
        let src = variant(body, call);
        let rows = outcomes(&src, "EncodeData", "InitOrStitch", 1, 2);
        assert!(certified(&rows), "{name}: {rows:?}");
    }
}

/// G2: whole-value movers of `core::mem` / `core::ptr` write every field
/// without a field store. Fault G2-F1: the five names dropped.
#[test]
fn w6v_control_a_whole_value_mover_refuses_the_struct() {
    const DEFAULT: &str = "impl Default for RingBuffer { fn default() -> Self { RingBuffer { size_: 0, data_: 0 as *mut u8, buffer_: 0 as *mut u8 } } }";
    for (name, body) in [
        (
            "mem::swap",
            "unsafe fn Mv(a: *mut RingBuffer, b: *mut RingBuffer) { core::mem::swap(&mut *a, &mut *b); }",
        ),
        (
            "mem::replace",
            "unsafe fn Mv(a: *mut RingBuffer, b: *mut RingBuffer) { let _ = core::mem::replace(&mut *a, *b); }",
        ),
        (
            "mem::take",
            "unsafe fn Mv(a: *mut RingBuffer, b: *mut RingBuffer) { let _ = core::mem::take(&mut *a); }",
        ),
        (
            "ptr::swap",
            "unsafe fn Mv(a: *mut RingBuffer, b: *mut RingBuffer) { core::ptr::swap(a, b); }",
        ),
        (
            "ptr::swap_nonoverlapping",
            "unsafe fn Mv(a: *mut RingBuffer, b: *mut RingBuffer) { core::ptr::swap_nonoverlapping(a, b, 1); }",
        ),
        (
            "ptr::write_volatile",
            "unsafe fn Mv(a: *mut RingBuffer, b: *mut RingBuffer) { core::ptr::write_volatile(a, *b); }",
        ),
    ] {
        let extra = if name == "mem::take" {
            format!("{DEFAULT}\n{body}")
        } else {
            body.to_owned()
        };
        let src = variant(&extra, "Mv(&mut (*s).ringbuffer_, &mut (*s).ringbuffer_);");
        assert_unproved(
            &outcomes(&src, "EncodeData", "InitOrStitch", 1, 2),
            &format!("{name} on a RingBuffer"),
        );
    }
}
