//! wave-6l, the extent prover (R666-2 step 1): C3 and its three controls.

/// Run the prover on `function`'s `(pointer, length)` parameter pair.
fn prove(input: &str, function: &str, pointer: usize, length: usize) -> Result<(), String> {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let did = tcx
            .hir_body_owners()
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == function)
            .expect("the function");
        super::extent_proof::prove_parameter_extent(tcx, did, pointer, length)
            .map_err(|refusal| refusal.reason)
    })
    .expect("fixture compiles")
}

const C3: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case)]
pub unsafe fn c3(mut p: *const u8, mut n: usize) -> u32 {
    let mut s: u32 = 0;
    let mut i: usize = 0;
    while i < n {
        s = s.wrapping_add(*p.offset(i as isize) as u32);
        i = i.wrapping_add(1);
    }
    s
}
pub unsafe fn c3_int(mut p: *const u8, mut n: i32) -> u32 {
    let mut s: u32 = 0;
    let mut i: i32 = 0 as i32;
    while i < n {
        s = s.wrapping_add(*p.offset(i as isize) as u32);
        i += 1;
    }
    s
}
pub unsafe fn c3_chain(mut p: *mut u8, mut n: usize, mut j: usize) {
    if j <= n {
        let mut i: usize = 0;
        while i < j {
            *p.offset(i as isize) = 0 as u8;
            i = i.wrapping_add(1);
        }
    }
}
pub unsafe fn c3_short_circuit(mut p: *const u8, mut n: usize) -> usize {
    let mut i: usize = 0;
    while *p.offset(i as isize) as i32 != 0 && i < n {
        i = i.wrapping_add(1);
    }
    i
}
pub unsafe fn c3_truncating(mut p: *const u8, mut n: usize) -> u32 {
    let mut s: u32 = 0;
    let mut i: usize = 0;
    while (i as u8 as usize) < n {
        s = s.wrapping_add(*p.offset(i as isize) as u32);
        i = i.wrapping_add(1);
    }
    s
}
pub unsafe fn c3_address_taken(mut p: *const u8, mut n: usize) -> u32 {
    let mut s: u32 = 0;
    let mut i: usize = 0;
    while i < n {
        let mut r = &mut n;
        *r = 2;
        s = s.wrapping_add(*p.offset(i as isize) as u32);
        i = i.wrapping_add(1);
    }
    s
}
pub unsafe fn c3_off_by_one(mut p: *const u8, mut n: usize) -> u32 {
    let mut s: u32 = 0;
    let mut i: usize = 0;
    while i <= n {
        s = s.wrapping_add(*p.offset(i as isize) as u32);
        i = i.wrapping_add(1);
    }
    s
}
"#;

/// C3 (design record §3) — a dominating bound: `while i < n { p[i] }`, over
/// `usize` and over C's `int` (the lower bound from `i = 0; i += 1`), and
/// through a chain `i < j <= n`.
#[test]
fn w6l_extent_c3_dominated_index() {
    assert_eq!(prove(C3, "c3", 0, 1), Ok(()));
    assert_eq!(prove(C3, "c3_int", 0, 1), Ok(()));
    assert_eq!(prove(C3, "c3_chain", 0, 1), Ok(()));
}

/// C3's controls (Codex 058 findings 2, 4, 5) and the off-by-one: each is
/// refused.
/// - the read precedes its guard (`*p.add(i) != 0 && i < n`);
/// - the guard is on a truncated copy (`(i as u8 as usize) < n`);
/// - the companion is written through its address between guard and read;
/// - `i <= n` reads `p[n]`.
#[test]
fn w6l_extent_c3_controls_are_refused() {
    for function in [
        "c3_short_circuit",
        "c3_truncating",
        "c3_address_taken",
        "c3_off_by_one",
    ] {
        assert!(prove(C3, function, 0, 1).is_err(), "{function}");
    }
}
