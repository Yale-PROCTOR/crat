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
pub unsafe fn c3_guarded_return(mut p: *const u8, mut n: usize, mut i: usize) -> u8 {
    if i >= n {
        return 0 as u8;
    }
    *p.offset(i as isize)
}
pub unsafe fn c3_null_checked(mut p: *const u8, mut n: usize) -> u32 {
    if p.is_null() {
        return 0 as u32;
    }
    let mut s: u32 = 0;
    let mut i: usize = 0;
    while i < n {
        s = s.wrapping_add(*p.offset(i as isize) as u32);
        i = i.wrapping_add(1);
    }
    s
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
pub unsafe fn c3_negative(mut p: *const u8, mut n: usize) -> u8 {
    if n > 0 as usize {
        return *p.offset(-(1 as i32) as isize);
    }
    0 as u8
}
pub unsafe fn c3_signed_negative(mut p: *const u8, mut n: i32) -> u32 {
    let mut s: u32 = 0;
    let mut i: i32 = -(1 as i32);
    while i < n {
        s = s.wrapping_add(*p.offset(i as isize) as u32);
        i += 1;
    }
    s
}
unsafe fn consume(mut q: *const u8) -> u8 {
    *q.offset(5 as isize)
}
pub unsafe fn c3_handed(mut p: *const u8, mut n: usize) -> u8 {
    if n > 0 as usize {
        return consume(p);
    }
    0 as u8
}
pub unsafe fn c3_wide_cast(mut p: *const u8, mut n: usize) -> u32 {
    let mut q = p as *const u32;
    if n > 0 as usize {
        return *q;
    }
    0 as u32
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
    // The read sits on the comparison's FALSE edge (`if i >= n { return }`).
    assert_eq!(prove(C3, "c3_guarded_return", 0, 1), Ok(()));
    // `p.is_null()` reads nothing and keeps nothing (the probe on the 112).
    assert_eq!(prove(C3, "c3_null_checked", 0, 1), Ok(()));
}

/// C3's controls (Codex 058 findings 2, 4, 5) and the off-by-one: each is
/// refused.
/// - the read precedes its guard (`*p.add(i) != 0 && i < n`);
/// - the guard is on a truncated copy (`(i as u8 as usize) < n`);
/// - the companion is written through its address between guard and read;
/// - `i <= n` reads `p[n]`;
/// - `p[-1]`, and a signed index that starts at `-1`, read before `p`;
/// - `p` handed to a callee (step 3's summaries);
/// - `p` read as a `u32` with only `n >= 1` byte (step 2's C7).
#[test]
fn w6l_extent_c3_controls_are_refused() {
    for (function, reason) in [
        ("c3_short_circuit", "access-unproven:upper"),
        ("c3_truncating", "access-unproven:upper"),
        ("c3_address_taken", "companion-written"),
        ("c3_off_by_one", "access-unproven:upper"),
        ("c3_negative", "access-unproven:lower"),
        ("c3_signed_negative", "access-unproven:lower"),
        ("c3_handed", "handed-to:consume"),
        ("c3_wide_cast", "access-through-a-cast-or-merged-pointer"),
    ] {
        assert_eq!(
            prove(C3, function, 0, 1),
            Err(reason.to_owned()),
            "{function}"
        );
    }
}
