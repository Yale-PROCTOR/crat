//! **R476-1 (USER ruling, relay 045): frame-bounded retention.**
//!
//! A positive-retention receipt at a bridging store is discharged when
//!   (1) the subject is dead after the store (MIR liveness),
//!   (2) the container is a non-escaping stack local of the same function, and
//!   (3) every callee receiving the container's address carries a no-retention
//!       certificate at that argument position (unknown ⇒ held).
//!
//! The shape is json.h `json_parse_ex` (`state.src = src;` then
//! `json_get_value_size(&mut state, …)`), reduced. bzip2's
//! `BZ2_bzBuffToBuffCompress` has the same (1) and (2) but fails (3), because
//! `BZ2_bzCompressInit` retains `&strm` — measured, and the control below is
//! that case.
use super::decision::raw_boundary::RetentionVerdict;

const READER: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
#[repr(C)]
pub struct State { pub src: *const u8, pub size: usize, pub offset: usize }
unsafe fn read_one(mut st: *mut State) -> i32 {
    let mut b = *((*st).src).offset((*st).offset as isize);
    (*st).offset = ((*st).offset).wrapping_add(1);
    return b as i32;
}
pub unsafe fn parse(mut src: *const u8, mut size: usize) -> i32 {
    let mut state = State { src: 0 as *const u8, size: 0, offset: 0 };
    if src.is_null() { return 0; }
    state.src = src;
    state.size = size;
    return read_one(&mut state);
}
"#;

/// `(verdict, reason)` of the retention row for `function` at `argument`.
fn retention_row(input: &str, function: &str, argument: usize) -> (String, String) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decision table");
        let tsv = &ctx.raw_boundary_artifacts.retention;
        let header = tsv.lines().next().expect("retention header");
        let ix = |name: &str| {
            header
                .split('\t')
                .position(|c| c == name)
                .unwrap_or_else(|| panic!("column {name} in {header}"))
        };
        let (f, a, v, r) = (
            ix("function"),
            ix("argument_index"),
            ix("verdict"),
            ix("reason"),
        );
        let row = tsv
            .lines()
            .skip(1)
            .map(|line| line.split('\t').collect::<Vec<_>>())
            .find(|c| c[f].ends_with(function) && c[a] == argument.to_string())
            .unwrap_or_else(|| panic!("no retention row for {function} arg{argument}:\n{tsv}"));
        (row[v].to_owned(), row[r].to_owned())
    })
    .expect("fixture compiler context")
}

/// **W6O-FB-1 — the delivering witness.** All three clauses hold, so the field
/// store is discharged and the row is `no-retain` with the typed receipt.
#[test]
fn wave6o_frame_bounded_store_is_discharged() {
    let (verdict, reason) = retention_row(READER, "parse", 0);
    assert_eq!(verdict, "no-retain", "reason={reason}");
    assert!(
        reason.contains("retention-discharged:frame-bounded"),
        "the discharge is receipted: {reason}"
    );
    assert!(
        reason.contains("container=") && reason.contains("callees="),
        "the receipt names the container and the callees it rests on: {reason}"
    );
}

/// **Control 1 — the subject is read after the store**, so clause (1) fails.
#[test]
fn wave6o_a_subject_read_after_the_store_is_not_frame_bounded() {
    let input = READER.replace(
        "    return read_one(&mut state);",
        "    let mut r = read_one(&mut state);\n    return r + (*src.offset(1 as isize)) as i32;",
    );
    let (verdict, _) = retention_row(&input, "parse", 0);
    assert_eq!(verdict, "retains");
}

/// **Control 2 — the container is a parameter's pointee**, so clause (2) fails:
/// the store target's root is not a local of this frame, and the caller keeps
/// the container after the call.
#[test]
fn wave6o_a_container_reached_through_a_parameter_is_not_frame_bounded() {
    const THROUGH_A_PARAMETER: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
#[repr(C)]
pub struct State { pub src: *const u8, pub size: usize, pub offset: usize }
unsafe fn read_one(mut st: *mut State) -> i32 {
    let mut b = *((*st).src).offset((*st).offset as isize);
    (*st).offset = ((*st).offset).wrapping_add(1);
    return b as i32;
}
pub unsafe fn parse(mut src: *const u8, mut size: usize, mut out: *mut State) -> i32 {
    if src.is_null() { return 0; }
    (*out).src = src;
    (*out).size = size;
    return read_one(out);
}
"#;
    let (verdict, _) = retention_row(THROUGH_A_PARAMETER, "parse", 0);
    assert_ne!(verdict, "no-retain");
}

/// **Control 3 — a callee that receives the container and RETAINS it**, so
/// clause (3) fails. This is bzip2's shape (`BZ2_bzCompressInit` stores
/// `&strm` into the heap state it allocates).
#[test]
fn wave6o_a_retaining_container_callee_keeps_the_hold() {
    let input = READER.replace(
        "pub unsafe fn parse",
        "static mut KEPT: *mut State = 0 as *mut State;\nunsafe fn init(mut st: *mut State) { KEPT = st; }\npub unsafe fn parse",
    )
    .replace("    state.src = src;", "    init(&mut state);\n    state.src = src;");
    let (verdict, _) = retention_row(&input, "parse", 0);
    assert_eq!(verdict, "retains");
}

/// **Control 4 — the container leaves the frame by value**, so clause (2)
/// fails on escape rather than on rooting. This is the corpus shape of ht
/// `ht_iterator` (`return it;`) and lodepng `ucvector_init` (`return v;`),
/// both of which the measurement found as near-misses.
#[test]
fn wave6o_a_returned_container_is_not_frame_bounded() {
    const RETURNED: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
#[repr(C)]
pub struct State { pub src: *const u8, pub size: usize, pub offset: usize }
unsafe fn read_one(mut st: *mut State) -> i32 {
    let mut b = *((*st).src).offset((*st).offset as isize);
    (*st).offset = ((*st).offset).wrapping_add(1);
    return b as i32;
}
pub unsafe fn parse(mut src: *const u8, mut size: usize) -> State {
    let mut state = State { src: 0 as *const u8, size: 0, offset: 0 };
    state.src = src;
    state.size = size;
    read_one(&mut state);
    return state;
}
"#;
    let (verdict, _) = retention_row(RETURNED, "parse", 0);
    assert_eq!(verdict, "retains");
}

/// **Control 5 (R477-4a, main 060d) — an INTERMEDIATE ancestor is read after
/// the store.** `src -> mid -> cur` is one provenance chain; the store carries
/// `cur`, and both the root (`src`) and the stored operand (`cur`) are dead
/// afterwards, so condition (1) asked of those two alone would discharge it.
/// It must be held: `mid` carries the same provenance and is read after the
/// store, so the retained pointer's value is still in use in this frame.
#[test]
fn wave6o_a_live_intermediate_ancestor_keeps_the_hold() {
    const REBORROWED: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
#[repr(C)]
pub struct State { pub src: *const u8, pub size: usize, pub offset: usize }
unsafe fn read_one(mut st: *mut State) -> i32 {
    let mut b = *((*st).src).offset((*st).offset as isize);
    (*st).offset = ((*st).offset).wrapping_add(1);
    return b as i32;
}
pub unsafe fn parse(mut src: *const u8, mut size: usize) -> i32 {
    let mut state = State { src: 0 as *const u8, size: 0, offset: 0 };
    if src.is_null() { return 0; }
    let mut mid = src;
    let mut cur = mid;
    state.src = cur;
    state.size = size;
    let mut n = read_one(&mut state);
    return n + (*mid.offset(1 as isize)) as i32;
}
"#;
    let (verdict, reason) = retention_row(REBORROWED, "parse", 0);
    assert_eq!(verdict, "retains", "reason={reason}");
}
