//! wave-6l, the extent prover (R666-2 step 1): C3 and its three controls.

/// Run the prover on `function`'s `(pointer, length)` parameter pair.
fn prove(input: &str, function: &str, pointer: usize, length: usize) -> Result<(), String> {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let did = tcx
            .hir_body_owners()
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == function)
            .expect("the function");
        super::extent_proof::prove_parameter_extent(tcx, did, pointer, length)
            .map(|_| ())
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
pub unsafe fn c3_wrapping_sub(mut p: *const u8, mut n: usize) -> u8 {
    let mut i: usize = 0;
    if i < n.wrapping_sub(1) {
        return *p.offset(i as isize);
    }
    0 as u8
}
pub unsafe fn c3_countdown(mut p: *const u8, mut n: usize) -> u8 {
    let mut i: usize = n;
    loop {
        let fresh = i;
        i = i.wrapping_sub(1);
        if !(fresh > 0 as usize) {
            break;
        }
    }
    *p.offset(n as isize)
}
unsafe fn parse(mut s: *mut *const u8) -> u8 {
    *(*s).offset(500 as isize)
}
pub unsafe fn c3_address_of_copy(mut p: *const u8, mut n: usize) -> u8 {
    let mut s = p;
    parse(&mut s)
}
pub unsafe fn c3_reborrowed_copy(mut p: *const u8, mut n: usize) -> u8 {
    let mut q = p.offset(100 as isize);
    let mut r = &mut q;
    **r
}
unsafe fn add(mut q: *const u8, mut k: usize) -> *const u8 {
    let mut first = *q.offset(500 as isize);
    q
}
pub unsafe fn c3_named_add(mut p: *const u8, mut n: usize) -> u8 {
    if n > 0 as usize {
        let mut q = add(p, 0 as usize);
        return *q;
    }
    0 as u8
}
pub unsafe fn c3_tainted_compare(mut p: *const u8, mut n: usize, mut q: *const u8) -> u8 {
    let mut w = (p as *const u32).add(1 as usize) as *const u8;
    let mut r = p;
    if n >= 1 as usize && r < w {
        return *r.offset(3 as isize);
    }
    0 as u8
}
pub unsafe fn c3_same_width_sign(mut p: *const u8, mut n: i32, mut u: u32) -> u8 {
    let mut k = u as i32;
    if k < n {
        return *p.offset(k as isize);
    }
    0 as u8
}
unsafe fn is_null(mut q: *const u8) -> bool {
    *q.offset(500 as isize) as i32 == 0 as i32
}
pub unsafe fn c3_named_is_null(mut p: *const u8, mut n: usize) -> u8 {
    if n > 0 as usize && !is_null(p) {
        return *p;
    }
    0 as u8
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
/// - `p` read as a `u32` with only `n >= 1` byte (step 2's C7);
/// - (relay 066 review) an unsigned `n - 1` that wraps at `n = 0`; a
///   countdown loop whose exit edge must not vanish; a derived copy whose
///   address is taken; a local helper named `add`; a comparison against a
///   pointer cast to another width; a same-width `u32 as i32`.
#[test]
fn w6l_extent_c3_controls_are_refused() {
    let wrong = [
        ("c3_short_circuit", "access-unproven:upper"),
        // (B5: `i as isize` keeps its value only when `i` is bounded by `n`,
        // and a truncated guard bounds nothing, so the offset has no lower
        // bound either.)
        ("c3_truncating", "access-unproven:lower"),
        ("c3_address_taken", "companion-written"),
        ("c3_off_by_one", "access-unproven:upper"),
        ("c3_negative", "access-unproven:lower"),
        ("c3_signed_negative", "access-unproven:lower"),
        ("c3_handed", "handed-to:consume"),
        ("c3_wide_cast", "access-through-a-cast-or-merged-pointer"),
        // The relay 066 review (B1-B5):
        ("c3_wrapping_sub", "access-unproven:upper"),
        ("c3_countdown", "access-unproven:upper"),
        ("c3_address_of_copy", "address-of-a-derived-pointer"),
        ("c3_reborrowed_copy", "address-of-a-derived-pointer"),
        ("c3_named_add", "handed-to:add"),
        ("c3_named_is_null", "handed-to:is_null"),
        ("c3_tainted_compare", "access-unproven:upper"),
        ("c3_same_width_sign", "access-unproven:lower"),
    ]
    .into_iter()
    .filter_map(|(function, reason)| {
        let got = prove(C3, function, 0, 1);
        (got != Err(reason.to_owned())).then(|| format!("{function}: {got:?}, want {reason}"))
    })
    .collect::<Vec<_>>();
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// Relay 067 (R669-3(c)) — the runtime harness's positive witness, ht's
/// `ht_set_entry(entries, capacity, ..)`: every index is `hash & (capacity −
/// 1)`, stepped by one and wrapped to 0 at `capacity`, so `capacity` is the
/// extent. At 52 both call sites build the slice with the fallback extent,
/// and the harness's 466,550-word input panics at index 131,072 (`capacity`
/// is 1,048,576 there).
const HT: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types)]
extern "C" {
    fn strcmp(a: *const i8, b: *const i8) -> i32;
    fn strdup(s: *const i8) -> *mut i8;
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct ht_entry {
    pub key: *const i8,
    pub value: *mut core::ffi::c_void,
}
unsafe fn hash_key(mut key: *const i8) -> u64 {
    let mut hash: u64 = 14695981039346656037;
    let mut p = key;
    while *p != 0 {
        hash ^= *p as u8 as u64;
        hash = hash.wrapping_mul(1099511628211);
        p = p.offset(1);
    }
    hash
}
pub unsafe extern "C" fn ht_set_entry(mut entries: *mut ht_entry, mut capacity: u64, mut key: *const i8, mut value: *mut core::ffi::c_void, mut plength: *mut u64) -> *const i8 {
    let mut hash = hash_key(key);
    let mut index = hash & capacity.wrapping_sub(1 as i32 as u64);
    while !((*entries.offset(index as isize)).key).is_null() {
        if strcmp(key, (*entries.offset(index as isize)).key) == 0 as i32 {
            (*entries.offset(index as isize)).value = value;
            return (*entries.offset(index as isize)).key;
        }
        index = index.wrapping_add(1);
        if index >= capacity {
            index = 0 as i32 as u64;
        }
    }
    if !plength.is_null() {
        key = strdup(key);
        if key.is_null() {
            return 0 as *const i8;
        }
        *plength = (*plength).wrapping_add(1);
    }
    (*entries.offset(index as isize)).key = key as *mut i8;
    (*entries.offset(index as isize)).value = value;
    return key;
}
pub unsafe fn masked_by_another(mut p: *const u8, mut n: u64, mut m: u64, mut h: u64) -> u8 {
    *p.offset((h & m.wrapping_sub(1 as i32 as u64)) as isize)
}
pub unsafe fn masked_by_two_less(mut p: *const u8, mut n: u64, mut h: u64) -> u8 {
    *p.offset((h & n.wrapping_sub(2 as i32 as u64)) as isize)
}
"#;

/// The mask premise (relay 067): `x & (n − 1)` is below the length `n`,
/// taken where `n` is nonzero wherever the callee reads (at `n = 0` the C
/// mask is all ones). ht's own sites pass 16 and doublings of it.
#[test]
fn w6l_extent_ht_set_entry_is_bounded_by_its_capacity() {
    let premises = ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(HT),
        |tcx| {
            let did = tcx
                .hir_body_owners()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == "ht_set_entry")
                .expect("the function");
            super::extent_proof::prove_parameter_extent(tcx, did, 0, 1)
                .map(|proof| proof.premises)
                .map_err(|refusal| refusal.reason)
        },
    )
    .expect("fixture compiles");
    assert_eq!(premises, Ok(vec!["mask-of-length"]));
}

/// Its controls: a mask by ANOTHER integer's `− 1`, and a mask by `n − 2`,
/// are not the length's premise.
#[test]
fn w6l_extent_masks_other_than_the_length_are_refused() {
    for function in ["masked_by_another", "masked_by_two_less"] {
        assert!(prove(HT, function, 0, 1).is_err(), "{function}");
    }
}
