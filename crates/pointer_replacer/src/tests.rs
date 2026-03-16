use super::*;

fn run_test(code: &str, includes: &[&str], excludes: &[&str]) {
    let config = Config::default();
    let (s, _) =
        ::utils::compilation::run_compiler_on_str(code, |tcx| replace_local_borrows(&config, tcx))
            .unwrap();
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    for include in includes {
        assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
    }
    for exclude in excludes {
        assert!(
            !s.contains(exclude),
            "Expected not to find `{exclude}` in:\n{s}",
        );
    }
}

#[test]
fn test_local_ptr_to_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    return *q;
}
"#,
        &["&mut"],
        &["*mut"],
    );
}

// ===== Cross-PtrKind assignment tests (same type, no cast) =====

/// Raw q = OptRef p: p is promoted (OptRef), q copies p then p is used again,
/// invalidating q's copy-loan → q demoted to Raw. Conversion: raw_from_opt_ref.
#[test]
fn test_raw_eq_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    *p = 20 as libc::c_int;
    return *q;
}
"#,
        &["null", "Option<&mut"],
        &[],
    );
}

/// OptRef q = Raw p: p has overlapping borrow conflict → demoted to Raw.
/// q = p after conflict, used simply → promoted to OptRef. Conversion: opt_ref_from_raw.
#[test]
fn test_ref_eq_raw() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    return *q;
}
"#,
        &[".as_ref()", "Option<&i32>"],
        &[],
    );
}

/// Raw q = Slice p: p uses .offset() → Arr + promoted = Slice. q copies p,
/// then p used again → q's loan invalidated → q Raw. Conversion: raw_from_slice.
#[test]
fn test_raw_eq_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    *p.offset(2 as isize) = 30 as libc::c_int;
    return *q;
}
"#,
        &[".as_", "_ptr()", "&mut [i32]"],
        &[],
    );
}

/// OptRef q = Slice p: p uses .offset() → Slice. q = p (no array ops,
/// fatness doesn't propagate) → Ptr + promoted = OptRef. Conversion: opt_ref_from_slice.
#[test]
fn test_ref_eq_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    return *q;
}
"#,
        &[".first()", "Option<&i32>", "&mut [i32]"],
        &[],
    );
}

/// Slice q = Raw p: p has overlapping borrow conflict → demoted → Raw.
/// q = p, then q does array ops → Arr + promoted = Slice. Conversion: slice_from_raw.
#[test]
fn test_slice_eq_raw() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    *q.offset(0 as isize) = 30 as libc::c_int;
    return *q.offset(0 as isize);
}
"#,
        &["from_raw_parts_mut", "&mut [i32]"],
        &[],
    );
}

/// Slice q = Slice p: both p and q use .offset() → both Arr + promoted = Slice.
/// Conversion: slice_from_slice.
#[test]
fn test_slice_eq_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    *q.offset(0 as isize) = 30 as libc::c_int;
    return *q.offset(1 as isize);
}
"#,
        &["&mut [i32]"],
        &["*mut"],
    );
}

// ===== Bytemuck type cast tests (same-size numerics) =====

/// OptRef q = OptRef p with type cast: both promoted (OptRef), but p is c_int
/// and q is c_uint. Same-size numerics → bytemuck::cast_ref.
/// Conversion: opt_ref_from_opt_ref (bytemuck branch).
#[test]
fn test_ref_eq_ref_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_uint = p as *mut libc::c_uint;
    return *q as libc::c_int;
}
"#,
        &["bytemuck::cast_ref", "Option<&u32>", "Option<&mut i32>"],
        &["*mut"],
    );
}

/// OptRef q = Slice p with type cast: p uses .offset() → Slice.
/// q = p (cast, no array ops) → OptRef. Same-size numerics → bytemuck::cast_ref.
/// Conversion: opt_ref_from_slice (bytemuck branch).
#[test]
fn test_ref_eq_slice_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_uint = p as *mut libc::c_uint;
    return *q as libc::c_int;
}
"#,
        &["bytemuck::cast_ref", "Option<&u32>", "&mut [i32]"],
        &["*mut"],
    );
}

/// Slice q = Slice p with type cast: both use .offset() → both Slice.
/// p is c_int, q is c_uint. Same-size numerics → bytemuck::cast_slice_mut.
/// Conversion: slice_from_slice (bytemuck branch).
#[test]
fn test_slice_eq_slice_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_uint = p as *mut libc::c_uint;
    *q.offset(0 as isize) = 30 as libc::c_uint;
    return *q.offset(1 as isize) as libc::c_int;
}
"#,
        &["bytemuck::cast_slice_mut", "&mut [u32]", "&mut [i32]"],
        &["*mut"],
    );
}

// ===== Non-bytemuck type cast tests =====
// For raw_from_*, opt_ref_from_raw, slice_from_raw: any different types trigger
// the cast branch (no bytemuck path exists). Uses c_int vs c_short.
// For opt_ref_from_opt_ref, opt_ref_from_slice: different-size numerics
// (c_int vs c_short) fail same_size → non-bytemuck else branch.
// For slice_from_slice: at least one non-numeric type needed (struct Pair)
// since all numerics go to bytemuck regardless of size.

/// Raw q = OptRef p, with type cast. q demoted via separate overlapping
/// borrow on y, then reassigned from OptRef p.
/// Conversion: raw_from_opt_ref (need_cast branch).
#[test]
fn test_raw_eq_ref_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut y: libc::c_short = 0 as libc::c_short;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_short = &mut y;
    let mut s: *mut libc::c_short = &mut y;
    *q = 1 as libc::c_short;
    *s = 2 as libc::c_short;
    q = p as *mut libc::c_short;
    return *q as libc::c_int;
}
"#,
        &["as *mut _ as *mut _", "null_mut", "Option<&mut i32>"],
        &["bytemuck"],
    );
}

/// Raw q = Slice p, with type cast. q demoted via separate overlapping
/// borrow on y, then reassigned from Slice p.
/// Conversion: raw_from_slice (need_cast branch).
#[test]
fn test_raw_eq_slice_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut y: libc::c_short = 0 as libc::c_short;
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_short = &mut y;
    let mut s: *mut libc::c_short = &mut y;
    *q = 1 as libc::c_short;
    *s = 2 as libc::c_short;
    q = p as *mut libc::c_short;
    return *q as libc::c_int;
}
"#,
        &["as_mut_ptr() as *mut _", "&mut [i32]"],
        &["bytemuck"],
    );
}

/// OptRef q = Raw p, with type cast. p has overlapping borrow conflict → Raw.
/// q = p with cast, used simply → OptRef.
/// Conversion: opt_ref_from_raw (need_cast branch).
#[test]
fn test_ref_eq_raw_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    let mut q: *mut libc::c_short = p as *mut libc::c_short;
    return *q as libc::c_int;
}
"#,
        &["as *const i16", ".as_ref()", "Option<&i16>"],
        &["bytemuck"],
    );
}

/// OptRef q = OptRef p, with type cast. Both promoted but p is c_int, q is c_short.
/// Different-size numerics → same_size fails → non-bytemuck cast.
/// Conversion: opt_ref_from_opt_ref (pointer-cast else branch).
#[test]
fn test_ref_eq_ref_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_short = p as *mut libc::c_short;
    return *q as libc::c_int;
}
"#,
        &[
            "as *const _ as *const i16",
            "Option<&i16>",
            "Option<&mut i32>",
        ],
        &["bytemuck"],
    );
}

/// OptRef q = Slice p, with type cast. p uses .offset() → Slice.
/// q = p (cast, no array ops) → OptRef. Different-size numerics → non-bytemuck cast.
/// Conversion: opt_ref_from_slice (pointer-cast else branch).
#[test]
fn test_ref_eq_slice_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_short = p as *mut libc::c_short;
    return *q as libc::c_int;
}
"#,
        &["as *const _ as *const _", ".first()", "&mut [i32]"],
        &["bytemuck"],
    );
}

/// Slice q = Raw p, with type cast. p has overlapping borrow conflict → Raw.
/// q = p with cast, uses .offset() → Slice.
/// Conversion: slice_from_raw (need_cast branch).
#[test]
fn test_slice_eq_raw_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    let mut q: *mut libc::c_short = p as *mut libc::c_short;
    *q.offset(0 as isize) = 30 as libc::c_short;
    return *q.offset(0 as isize) as libc::c_int;
}
"#,
        &["from_raw_parts_mut", "as *mut _", "&mut [i16]"],
        &["bytemuck"],
    );
}

/// Slice q = Slice p, with type cast. Both use .offset() → both Slice.
/// p is struct Pair (non-numeric), q is c_int. At least one non-numeric type
/// → non-bytemuck cast via from_raw_parts.
/// Conversion: slice_from_slice (pointer-cast else branch).
#[test]
fn test_slice_eq_slice_cast() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Pair {
    pub a: libc::c_int,
    pub b: libc::c_int,
}
impl Copy for Pair {}
impl Clone for Pair {
    fn clone(&self) -> Self { *self }
}
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [Pair; 10] = [Pair { a: 0, b: 0 }; 10];
    let mut p: *mut Pair = arr.as_mut_ptr();
    (*p.offset(0 as isize)).a = 10 as libc::c_int;
    (*p.offset(1 as isize)).a = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p as *mut libc::c_int;
    *q.offset(0 as isize) = 30 as libc::c_int;
    return *q.offset(1 as isize);
}
"#,
        &["from_raw_parts_mut", "as *mut i32", "&mut [i32]"],
        &["bytemuck"],
    );
}

// ===== projected_expr tests: offset and cast projections on Slice base =====
// When the RHS is `p.offset(n)` or `(p as *mut T).offset(n)` and p is Slice,
// projected_expr transforms the projections before passing to the conversion
// function. Offset becomes `[(n) as usize..]`; non-usize cast calls
// slice_from_slice internally.

// --- Single offset ---

/// OptRef q = Slice p.offset(2): projected_expr transforms offset to
/// slice range `(p)[(2) as usize..]`, then opt_ref_from_slice → .first().
#[test]
fn test_ref_eq_slice_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p.offset(2 as isize);
    return *q;
}
"#,
        &["as usize..]", ".first()", "Option<&i32>"],
        &["*mut"],
    );
}

/// Slice q = Slice p.offset(2): projected_expr transforms offset to
/// slice range, then slice_from_slice → &mut(...).
#[test]
fn test_slice_eq_slice_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p.offset(2 as isize);
    *q.offset(0 as isize) = 30 as libc::c_int;
    return *q.offset(0 as isize);
}
"#,
        &["as usize..]", "&mut [i32]"],
        &["*mut"],
    );
}

// --- Multiple offsets ---

/// OptRef q = Slice p.offset(2).offset(1): projected_expr chains two
/// offset projections into nested slice ranges.
#[test]
fn test_ref_eq_slice_multi_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p.offset(2 as isize).offset(1 as isize);
    return *q;
}
"#,
        &[
            "(2 as isize) as usize..]",
            "(1 as isize) as usize..]",
            ".first()",
        ],
        &["*mut"],
    );
}

/// Slice q = Slice p.offset(2).offset(1): projected_expr chains two
/// offset projections, then slice_from_slice → &mut(...).
#[test]
fn test_slice_eq_slice_multi_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p.offset(2 as isize).offset(1 as isize);
    *q.offset(0 as isize) = 30 as libc::c_int;
    return *q.offset(0 as isize);
}
"#,
        &[
            "(2 as isize) as usize..]",
            "(1 as isize) as usize..]",
            "&mut [i32]",
        ],
        &["*mut"],
    );
}

// ===== addr_of tests: RHS is `&mut x` (taking address of a local variable) =====
// The `addr_of` branch handles RHS expressions of the form `&mut x`.
// 3 PtrKind contexts (Raw, OptRef, Slice) × 2-3 sub-cases (need_cast, ty_updated).

// --- Raw context ---

/// addr_of with Raw context, no cast: overlapping borrows on x demote both
/// pointers to Raw. Output: `&raw mut (x)`.
#[test]
fn test_addr_of_raw() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    return *p;
}
"#,
        &["&raw mut"],
        &["Some(", "slice::from"],
    );
}

/// addr_of with Raw context, with cast: overlapping borrows + type cast.
/// Output: `&raw mut (x) as *mut i16`.
#[test]
fn test_addr_of_raw_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_short = &mut x as *mut libc::c_int as *mut libc::c_short;
    let mut r: *mut libc::c_short = &mut x as *mut libc::c_int as *mut libc::c_short;
    *p = 10 as libc::c_short;
    *r = 20 as libc::c_short;
    return *p as libc::c_int;
}
"#,
        &["&raw mut", "as *mut i16"],
        &["Some("],
    );
}

// --- OptRef context ---

/// addr_of with OptRef context, no cast: simple `&mut x` usage, no conflicts.
/// Output: `Some(&mut (x))`.
#[test]
fn test_addr_of_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    return *p;
}
"#,
        &["Some(&mut", "Option<&mut i32>"],
        &["*mut", "bytemuck"],
    );
}

/// addr_of with OptRef context, bytemuck cast: same-size numerics (c_int vs c_uint).
/// p is read-only so m=false → `Some(bytemuck::cast_ref::<_, u32>(&(x)))`.
#[test]
fn test_addr_of_ref_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_uint = &mut x as *mut libc::c_int as *mut libc::c_uint;
    return *p as libc::c_int;
}
"#,
        &["bytemuck::cast_ref", "Option<&u32>"],
        &["*mut"],
    );
}

/// addr_of with OptRef context, non-bytemuck cast: different-size numerics
/// (c_int vs c_short). p is read-only so m=false → `Some(&*(&raw const (x) as *const i16))`.
#[test]
fn test_addr_of_ref_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_short = &mut x as *mut libc::c_int as *mut libc::c_short;
    return *p as libc::c_int;
}
"#,
        &["&raw const", "as *const i16", "Some("],
        &["bytemuck"],
    );
}

// --- Slice context ---

/// addr_of with Slice context, no cast: `&mut x` with .offset() usage gives
/// p array_pointer status → Slice. Output: `std::slice::from_mut(&mut (x))`.
#[test]
fn test_addr_of_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p.offset(0 as isize) = 10 as libc::c_int;
    return *p.offset(0 as isize);
}
"#,
        &["slice::from_mut", "&mut [i32]"],
        &["*mut", "bytemuck"],
    );
}

/// addr_of with Slice context, bytemuck cast: same-size numerics (c_int vs c_uint)
/// with .offset() usage. Output: `std::slice::from_mut(bytemuck::cast_mut(&mut (x)))`.
#[test]
fn test_addr_of_slice_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_uint = &mut x as *mut libc::c_int as *mut libc::c_uint;
    *p.offset(0 as isize) = 10 as libc::c_uint;
    return *p.offset(0 as isize) as libc::c_int;
}
"#,
        &["bytemuck::cast_mut", "slice::from_mut", "&mut [u32]"],
        &["*mut"],
    );
}

/// addr_of with Slice context, non-bytemuck cast: different-size numerics
/// (c_int vs c_short) with .offset() usage.
/// Output: `std::slice::from_raw_parts_mut(&raw mut (x) as *mut _, 100000)`.
#[test]
fn test_addr_of_slice_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_short = &mut x as *mut libc::c_int as *mut libc::c_short;
    *p.offset(0 as isize) = 10 as libc::c_short;
    return *p.offset(0 as isize) as libc::c_int;
}
"#,
        &["from_raw_parts_mut", "&raw mut", "&mut [i16]"],
        &["bytemuck"],
    );
}

// --- Non-usize cast + offset ---

/// OptRef q = Slice (p as *mut c_uint).offset(2): projected_expr first
/// applies cast via slice_from_slice (bytemuck for same-size numerics),
/// then offset → `(bytemuck::cast_slice(p))[(2) as usize..]`.
#[test]
fn test_ref_eq_slice_cast_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_uint = (p as *mut libc::c_uint).offset(2 as isize);
    return *q as libc::c_int;
}
"#,
        &[
            "bytemuck::cast_slice",
            "as usize..]",
            ".first()",
            "Option<&u32>",
        ],
        &["*mut"],
    );
}

/// Slice q = Slice (p as *mut c_uint).offset(2): projected_expr first
/// applies cast via slice_from_slice (bytemuck), then offset →
/// `(bytemuck::cast_slice_mut(p))[(2) as usize..]`.
#[test]
fn test_slice_eq_slice_cast_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_uint = (p as *mut libc::c_uint).offset(2 as isize);
    *q.offset(0 as isize) = 30 as libc::c_uint;
    return *q.offset(0 as isize) as libc::c_int;
}
"#,
        &["bytemuck::cast_slice_mut", "as usize..]", "&mut [u32]"],
        &["*mut"],
    );
}

// ===== visit_expr code path tests =====

/// Binary pointer comparison (ExprKind::Binary with comparison ops on pointer-typed operands).
/// Both sides are transformed as PtrKind::Raw — OptRef pointers get converted via
/// `map_or(null_mut, ...)` for the comparison.
#[test]
fn test_ptr_comparison() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut y: libc::c_int = 43 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut q: *mut libc::c_int = &mut y;
    *p = 10 as libc::c_int;
    *q = 20 as libc::c_int;
    if p == q { return 1 as libc::c_int; }
    return 0 as libc::c_int;
}
"#,
        &["Option<&mut i32>", "null_mut"],
        &[],
    );
}

/// Function call with pointer argument — local function, sig_decs lookup succeeds.
/// bar's parameter is transformed to OptRef, and the call site converts p accordingly.
#[test]
fn test_ptr_call_arg() {
    run_test(
        r#"
use ::libc;
unsafe fn bar(p: *mut libc::c_int) -> libc::c_int { return *p; }
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    return bar(p);
}
"#,
        &["Option<&i32>", "as_deref()"],
        &[],
    );
}

/// `.is_null()` on OptRef pointer → `.is_none()`.
#[test]
fn test_is_null_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    if p.is_null() { return 0 as libc::c_int; }
    return *p;
}
"#,
        &["is_none", "Option<&mut i32>"],
        &["is_null"],
    );
}

/// `.is_null()` on Slice pointer → `.is_empty()`.
#[test]
fn test_is_null_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p.offset(0 as isize) = 10 as libc::c_int;
    if p.is_null() { return 0 as libc::c_int; }
    return *p.offset(0 as isize);
}
"#,
        &["is_empty", "&mut [i32]"],
        &["is_null"],
    );
}

/// Return statement with raw pointer return type — p is internally OptRef
/// but the function returns `*mut c_int`, so the return coerces p to Raw.
#[test]
fn test_return_raw_ptr() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> *mut libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    return p;
}
"#,
        &["&raw mut"],
        &["Option<", "&mut ["],
    );
}

/// Tuple return with a pointer element: p is promoted to Option<&mut>,
/// and the return expression must coerce the tuple element back to raw.
#[test]
fn test_return_tuple_with_ptr() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> (libc::c_int, *mut libc::c_int) {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    return (0 as libc::c_int, p);
}
"#,
        &["Option<&mut"],
        &[],
    );
}

/// Slice deref fallback: `*p` on a Slice variable without offset → `(p)[0]`.
/// When p is Slice but deref doesn't match the `&arr[start..]` pattern,
/// the else branch at line 296 produces `(*p)[0]`.
#[test]
fn test_deref_slice_no_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(1 as isize) = 10 as libc::c_int;
    *p = 20 as libc::c_int;
    return *p;
}
"#,
        &["[0]", "&mut [i32]"],
        &["*mut"],
    );
}

// ===== transform_ptr code path tests: null literal, if-else, block, cast_int =====

/// Null literal (`0 as *mut T`) assigned to OptRef pointer → `None`.
/// Exercises the `is_zero() + PtrCtx::Rhs(OptRef)` branch.
#[test]
fn test_null_ptr_opt_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    p = 0 as *mut libc::c_int;
    return if p.is_null() { 0 as libc::c_int } else { 1 as libc::c_int };
}
"#,
        &["None", "Option<&mut i32>"],
        &["null_mut"],
    );
}

/// Null literal (`0 as *mut T`) assigned to Slice pointer → `&mut []`.
/// Exercises the `is_zero() + PtrCtx::Rhs(Slice)` branch.
#[test]
fn test_null_ptr_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    p = 0 as *mut libc::c_int;
    return 0 as libc::c_int;
}
"#,
        &["&mut []", "&mut [i32]"],
        &["null_mut"],
    );
}

/// Null literal (`0 as *mut T`) assigned to Raw pointer → `std::ptr::null_mut()`.
/// Exercises the `is_zero() + PtrCtx::Rhs(Raw)` branch.
#[test]
fn test_null_ptr_raw() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    p = 0 as *mut libc::c_int;
    return *r;
}
"#,
        &["null_mut"],
        &["None"],
    );
}

/// Dereference of null literal: `*(0 as *mut T)`.
/// Exercises the `is_zero() + PtrCtx::Deref` branch, which returns `PtrKind::Raw(m)`
/// and leaves the expression unchanged. The result is a raw deref that passes through.
#[test]
fn test_deref_null() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = *(0 as *mut libc::c_int);
    return x;
}
"#,
        &["*(0"],
        &["Option<", "&mut ["],
    );
}

/// If-else (ternary) pointer expression: `p = if cond { &mut x } else { &mut y }`.
/// Exercises the `ExprKind::If` branch in `transform_ptr` — both branches
/// are recursively transformed.
#[test]
fn test_if_else_ptr() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut y: libc::c_int = 43 as libc::c_int;
    let mut cond: libc::c_int = 1 as libc::c_int;
    let mut p: *mut libc::c_int = if cond != 0 { &mut x } else { &mut y };
    *p = 10 as libc::c_int;
    return *p;
}
"#,
        &["Option<&mut i32>", "Some(&mut"],
        &["*mut"],
    );
}

/// Block-wrapped pointer expression: `p = { &mut x }`.
/// Exercises the `ExprKind::Block` branch in `transform_ptr` — the inner
/// expression is recursively transformed.
#[test]
fn test_block_ptr() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = { &mut x };
    *p = 10 as libc::c_int;
    return *p;
}
"#,
        &["Option<&mut i32>", "Some(&mut"],
        &["*mut"],
    );
}

/// Integer-to-pointer cast via usize bitwise op: `q = (p as usize | 0) as *mut c_int`.
/// Exercises the `cast_int` branch in `transform_ptr` — the Binary expression
/// prevents `unwrap_cast_and_paren` from stripping the usize cast, so `ptr_expr`
/// sees a Cast to usize and sets `cast_int = true`. q must be Raw (overlapping
/// borrow) to match `PtrCtx::Rhs(Raw)`. Uses `|` (not `+`) since `projected_expr`
/// only handles `BitAnd`/`BitOr` for `IntegerBinOp`.
#[test]
fn test_cast_int_ptr() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut y: libc::c_int = 43 as libc::c_int;
    let mut q: *mut libc::c_int = &mut y;
    let mut s: *mut libc::c_int = &mut y;
    *q = 1 as libc::c_int;
    *s = 2 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    q = (p as usize | 0 as usize) as *mut libc::c_int;
    return *q;
}
"#,
        &["as usize"],
        &[],
    );
}

// ===== as_ptr + Raw context tests (lines 549-565) =====

/// as_ptr + Raw, no cast: overlapping borrows from `.as_mut_ptr()` demote both
/// to Raw. Same types → `!need_cast`. Output: `(arr).as_mut_ptr()`.
#[test]
fn test_as_ptr_raw_no_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    let mut q: *mut libc::c_int = arr.as_mut_ptr();
    *p = 10 as libc::c_int;
    *q = 20 as libc::c_int;
    return *p;
}
"#,
        &["as_mut_ptr()"],
        &["Some(", "Option<"],
    );
}

/// as_ptr + Raw, with cast: overlapping borrows + type cast (c_int vs c_short).
/// Output: `(arr).as_mut_ptr() as *mut _`.
#[test]
fn test_as_ptr_raw_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_short = arr.as_mut_ptr() as *mut libc::c_short;
    let mut q: *mut libc::c_short = arr.as_mut_ptr() as *mut libc::c_short;
    *p = 10 as libc::c_short;
    *q = 20 as libc::c_short;
    return *p as libc::c_int;
}
"#,
        &["as_mut_ptr() as *mut"],
        &["Some(", "Option<"],
    );
}

// ===== as_ptr + OptRef context tests (lines 567-599) =====

/// as_ptr + OptRef, no cast: single borrow from `.as_mut_ptr()`, no overlap,
/// no offset → promoted to OptRef. Same types. Output: `Some(&mut (arr)[0])`.
#[test]
fn test_as_ptr_ref_no_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p = 10 as libc::c_int;
    return *p;
}
"#,
        &["Some(", "[0])"],
        &["*mut", "bytemuck"],
    );
}

/// as_ptr + OptRef, bytemuck cast: single borrow, c_int vs c_uint (same-size numerics).
/// Output: `Some(bytemuck::cast_mut::<_, u32>(&mut (arr)[0]))`.
#[test]
fn test_as_ptr_ref_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_uint = arr.as_mut_ptr() as *mut libc::c_uint;
    *p = 10 as libc::c_uint;
    return *p as libc::c_int;
}
"#,
        &["bytemuck::cast_", "[0])"],
        &["*mut"],
    );
}

/// as_ptr + OptRef, non-bytemuck cast: single borrow, c_int (4B) vs c_short (2B)
/// → different size → else branch. Output: `Some(&mut *(arr).as_mut_ptr() as *mut i16)`.
#[test]
fn test_as_ptr_ref_ptr_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_short = arr.as_mut_ptr() as *mut libc::c_short;
    *p = 10 as libc::c_short;
    return *p as libc::c_int;
}
"#,
        &["Some(", "as *"],
        &["bytemuck"],
    );
}

// ===== as_ptr + Slice + need_cast tests (lines 616-637) =====

/// as_ptr + Slice, bytemuck cast: same-size numerics (c_int ↔ c_uint) with offset.
/// Output: `bytemuck::cast_slice_mut(&mut (arr))`.
#[test]
fn test_as_ptr_slice_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_uint = arr.as_mut_ptr() as *mut libc::c_uint;
    *p.offset(0 as isize) = 10 as libc::c_uint;
    *p.offset(1 as isize) = 20 as libc::c_uint;
    return *p.offset(0 as isize) as libc::c_int;
}
"#,
        &["bytemuck::cast_slice"],
        &["from_raw_parts"],
    );
}

/// as_ptr + Slice, non-bytemuck cast: struct array cast to c_int pointer.
/// Non-numeric rhs_inner_ty → `from_raw_parts_mut`.
#[test]
fn test_as_ptr_slice_raw_parts() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Pair {
    pub a: libc::c_int,
    pub b: libc::c_int,
}
impl Copy for Pair {}
impl Clone for Pair {
    fn clone(&self) -> Self { *self }
}
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [Pair; 10] = [Pair { a: 0, b: 0 }; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr() as *mut libc::c_int;
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    return *p.offset(0 as isize);
}
"#,
        &["from_raw_parts"],
        &["bytemuck"],
    );
}

// ===== ByteStr tests (lines 700-732) =====

/// ByteStr + OptRef, u8: byte string literal used as `*const u8`, single deref
/// (no offset) → OptRef. `lhs_inner_ty == u8` → `.first()`.
#[test]
fn test_bytestr_opt_ref_u8() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut s: *const libc::c_uchar = b"hello\x00" as *const u8;
    return *s as libc::c_int;
}
"#,
        &[".first()"],
        &["*const", "bytemuck"],
    );
}

/// ByteStr + OptRef, numeric cast: byte string cast to `*const c_int`.
/// `lhs_inner_ty = i32` (numeric, not u8) → `bytemuck::cast_slice(...).first()`.
#[test]
fn test_bytestr_opt_ref_numeric() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut s: *const libc::c_int = b"hell" as *const u8 as *const libc::c_int;
    return *s;
}
"#,
        &["bytemuck::cast_slice", ".first()"],
        &["*const"],
    );
}

/// ByteStr + Slice, u8: byte string with offset → Slice. `lhs_inner_ty == u8`
/// → expression cloned.
#[test]
fn test_bytestr_slice_u8() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut s: *const libc::c_uchar = b"hello\x00" as *const u8;
    let a: libc::c_uchar = *s.offset(0 as isize);
    let b: libc::c_uchar = *s.offset(1 as isize);
    return (a as libc::c_int) + (b as libc::c_int);
}
"#,
        &["&[u8]"],
        &["*const", "bytemuck"],
    );
}

/// ByteStr + Slice, numeric cast: byte string cast to `*const c_int` with offset.
/// `lhs_inner_ty = i32` (not u8) → `bytemuck::cast_slice(...)`.
#[test]
fn test_bytestr_slice_numeric() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut s: *const libc::c_int = b"hellworl" as *const u8 as *const libc::c_int;
    let a: libc::c_int = *s.offset(0 as isize);
    let b: libc::c_int = *s.offset(1 as isize);
    return a + b;
}
"#,
        &["bytemuck::cast_slice"],
        &["*const"],
    );
}

// ===== Fallthrough tests (lines 734-755): struct field pointer access =====

/// Fallthrough + OptRef: struct field `s.data` is a `*mut c_int` → `PtrExprBaseKind::Other`.
/// Single borrow → promoted to OptRef.
#[test]
fn test_field_ptr_opt_ref() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Foo {
    pub data: *mut libc::c_int,
}
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut s: Foo = Foo { data: &mut x };
    let mut p: *mut libc::c_int = s.data;
    *p = 10 as libc::c_int;
    return *p;
}
"#,
        &["Option<&mut i32>"],
        &["*mut i32"],
    );
}

/// Fallthrough + Slice: struct field `s.data` with `.offset()` → Slice.
#[test]
fn test_field_ptr_slice() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Foo {
    pub data: *mut libc::c_int,
}
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut s: Foo = Foo { data: &mut x };
    let mut p: *mut libc::c_int = s.data;
    *p.offset(0 as isize) = 10 as libc::c_int;
    return *p.offset(0 as isize);
}
"#,
        &["&mut [i32]"],
        &["*mut i32"],
    );
}

// ===== slice_from_raw Branch A tests: method call (offset/as_mut_ptr/as_ptr) =====

/// slice_from_raw Branch A1 (no cast): `q = p.offset(2)` where p is Raw, q is Slice.
/// `method_call_name(p.offset(2))` → "offset" → skip null check, no cast needed.
#[test]
fn test_sfr_method_call_no_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 1 as libc::c_int;
    *r = 2 as libc::c_int;
    let mut q: *mut libc::c_int = p.offset(2 as isize);
    *q.offset(0 as isize) = 10 as libc::c_int;
    return *q.offset(0 as isize);
}
"#,
        &["from_raw_parts_mut", "p.offset"],
        &["is_null", "let _x"],
    );
}

/// slice_from_raw Branch A2 (with cast): `q = p.offset(2) as *mut c_short` where p is Raw.
/// `unwrap_cast_and_paren` strips cast → "offset" → Branch A, `need_cast=true` → `as *mut _`.
#[test]
fn test_sfr_method_call_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 1 as libc::c_int;
    *r = 2 as libc::c_int;
    let mut q: *mut libc::c_short = p.offset(2 as isize) as *mut libc::c_short;
    *q.offset(0 as isize) = 10 as libc::c_short;
    return *q.offset(0 as isize) as libc::c_int;
}
"#,
        &["from_raw_parts_mut", "as *mut _"],
        &["is_null", "let _x"],
    );
}

// ===== slice_from_raw Branch C tests: side effects =====
// A function call returning a raw pointer has side effects (Call is not whitelisted)
// and reaches the fallthrough path (PtrExprBaseKind::Other at line 1153).
// transform_ptr does NOT recurse into Call expressions, so slice_from_raw sees the
// full call expression and hits Branch C.

/// slice_from_raw Branch C1 (side effects, no cast): `q = identity(p)` where
/// identity is an extern function returning a raw pointer. `has_side_effects(Call)` → true,
/// same types → C1. Uses extern to avoid parameter transformation.
#[test]
fn test_sfr_side_effects_no_cast() {
    run_test(
        r#"
use ::libc;
extern "C" { fn identity(p: *mut libc::c_int) -> *mut libc::c_int; }
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut q: *mut libc::c_int = identity(&mut x);
    *q.offset(0 as isize) = 10 as libc::c_int;
    return *q.offset(0 as isize);
}
"#,
        &["let _x", "from_raw_parts_mut"],
        &["as *mut _"],
    );
}

/// slice_from_raw Branch C2 (side effects, with cast): `q = identity(p) as *mut c_short`.
/// `has_side_effects(Call)` → true, different types → need_cast → C2. Uses extern to
/// avoid parameter transformation.
#[test]
fn test_sfr_side_effects_cast() {
    run_test(
        r#"
use ::libc;
extern "C" { fn identity(p: *mut libc::c_int) -> *mut libc::c_int; }
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut q: *mut libc::c_short = identity(&mut x) as *mut libc::c_short;
    *q.offset(0 as isize) = 10 as libc::c_short;
    return *q.offset(0 as isize) as libc::c_int;
}
"#,
        &["let _x", "from_raw_parts_mut", "as *mut _"],
        &[],
    );
}

// ===== addr_of + pointer arithmetic tests =====

/// addr_of with cast + offset: `*(&mut x as *mut c_int as *mut c_char).offset(1) = 0`.
/// The addr_of block builds a slice via `std::slice::from_mut`, applies Cast via
/// bytemuck::cast_slice_mut, then Offset as range indexing. visit_expr converts
/// `*&mut slice[n..]` → `slice[n]`.
#[test]
fn test_addr_of_cast_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() {
    let mut x: libc::c_int = 0 as libc::c_int;
    *(&mut x as *mut libc::c_int as *mut libc::c_char)
        .offset(1 as libc::c_int as isize) = 0 as libc::c_char;
}

"#,
        &["bytemuck::cast_slice_mut", "slice::from_mut", "as usize..]"],
        &["*mut", "as *mut"],
    );
}

#[test]
fn test_interproc_negative_offset_propagation() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(
    mut end: *mut libc::c_int,
    mut count: libc::c_int,
) -> libc::c_int {
    let mut sum: libc::c_int = 0 as libc::c_int;
    let mut ptr: *mut libc::c_int = end;
    let mut i: libc::c_int = 0 as libc::c_int;
    while i < count {
        sum += *ptr;
        ptr = ptr.offset(-1);
        i += 1;
    }
    return sum;
}
pub unsafe extern "C" fn bar() -> libc::c_int {
    let mut arr: [libc::c_int; 5] = [1, 2, 3, 4, 5];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    let mut last_element: *mut libc::c_int = p.offset(4 as isize);
    return foo(last_element, 5 as libc::c_int);
}
"#,
        &[
            "let mut last_element: crate::slice_cursor::SliceCursor",
            "foo(last_element, 5 as libc::c_int)",
        ],
        &["let mut last_element: &[i32]"],
    );
}

#[test]
fn test_cursor_mut_to_ref_preserves_pos() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(
    mut end: *const libc::c_int,
    mut count: libc::c_int,
) -> libc::c_int {
    let mut sum: libc::c_int = 0 as libc::c_int;
    while count > 0 {
        sum += *end;
        end = end.offset(-1);
        count -= 1;
    }
    return sum;
}
pub unsafe extern "C" fn bar() -> libc::c_int {
    let mut arr: [libc::c_int; 6] = [1, 2, 3, 4, 5, 6];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p = 9 as libc::c_int;
    p = p.offset(1 as isize);
    p = p.offset(-1 as isize);
    let mut q: *const libc::c_int = p.offset(4 as isize) as *const libc::c_int;
    return foo(q, 1 as libc::c_int);
}
"#,
        &[".as_deref()"],
        &["SliceCursor::new((", ").as_slice())"],
    );
}

/// Fallthrough + Raw: overlapping borrows from struct field `s.data` → both demoted to Raw.
#[test]
fn test_field_ptr_raw() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Foo {
    pub data: *mut libc::c_int,
}
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut s: Foo = Foo { data: &mut x };
    let mut p: *mut libc::c_int = s.data;
    let mut q: *mut libc::c_int = s.data;
    *p = 10 as libc::c_int;
    *q = 20 as libc::c_int;
    return *p;
}
"#,
        &["s.data"],
        &["Option<", "&mut ["],
    );
}

/// Raw pointer mutability cast: `p` is *mut (writes through it), `q` is *const
/// (only compared). The comparison `p == q` requires matching types, so a cast
/// is inserted.
#[test]
fn test_raw_ptr_mutability_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 0 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut q: *mut libc::c_int = &mut x;
    *p = 1 as libc::c_int;
    return (p == q) as libc::c_int;
}
"#,
        &["*mut", "*const"],
        &[],
    );
}

/// Return type mutability: function returns a pointer that is never written through,
/// so the return type should become *const.
#[test]
fn test_return_type_mutability() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(mut x: *mut libc::c_int) -> *mut libc::c_int {
    return x;
}
"#,
        &["*const"],
        &[],
    );
}

/// Call-site cast: callee's return type mutability changes and the caller
/// needs a cast to match.
#[test]
fn test_call_site_return_type_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(mut x: *mut libc::c_int) -> *mut libc::c_int {
    return x;
}
pub unsafe extern "C" fn bar() {
    let mut x: libc::c_int = 0 as libc::c_int;
    let mut p: *mut libc::c_int = 0 as *mut libc::c_int;
    let mut q: *mut *mut libc::c_int = &mut p;
    *q = foo(&mut x);
}
"#,
        &["*const"],
        &[],
    );
}

mod ownership_analysis {
    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_hir::{ItemKind, OwnerNode, def_id::DefId};
    use rustc_middle::{mir::Local, ty::TyCtxt};
    use rustc_span::def_id::LocalDefId;

    use crate::{
        analyses::{
            output_params::compute_output_params,
            ownership::{
                AnalysisKind, CrateCtxt, Ownership, Param,
                ssa::{AnalysisResults, consume::Consume},
                whole_program::WholeProgramAnalysis,
            },
            type_qualifier::foster::mutability::mutability_analysis,
        },
        utils::rustc::RustProgram,
    };

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

    fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }

        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    fn analyze_program<'tcx>(
        program: &RustProgram<'tcx>,
    ) -> crate::analyses::ownership::whole_program::WholeProgramResults<'tcx> {
        let mutability_result = mutability_analysis(program);
        let aliases: FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>> =
            FxHashMap::default();
        let output_params = compute_output_params(program, &mutability_result, &aliases);
        let crate_ctxt = CrateCtxt::new(program);
        <WholeProgramAnalysis as AnalysisKind>::analyze(crate_ctxt, &output_params)
            .expect("ownership analysis should succeed")
    }

    fn find_function(program: &RustProgram<'_>, name: &str) -> DefId {
        program
            .functions
            .iter()
            .map(|did| did.to_def_id())
            .find(|&did| {
                let path = program.tcx.def_path_str(did);
                path.rsplit("::").next() == Some(name)
            })
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    #[test]
    fn ownership_from_option_and_display() {
        assert_eq!(Ownership::from(Some(true)), Ownership::Owning);
        assert_eq!(Ownership::from(Some(false)), Ownership::Transient);
        assert_eq!(Ownership::from(None), Ownership::Unknown);

        assert_eq!(Ownership::Owning.to_string(), "&move");
        assert_eq!(Ownership::Transient.to_string(), "&");
        assert_eq!(Ownership::Unknown.to_string(), "&any");
    }

    #[test]
    fn param_helpers_cover_normal_and_output_variants() {
        let normal = Param::Normal(7u8);
        assert!(!normal.is_output());
        assert_eq!(normal.clone().to_input(), 7);
        assert_eq!(normal.clone().to_output(), None);
        assert_eq!(normal.clone().expect_normal(), 7);

        let output = Param::Output(Consume {
            r#use: 11u8,
            def: 13u8,
        });
        assert!(output.is_output());
        assert_eq!(output.clone().to_input(), 11);
        assert_eq!(output.clone().to_output(), Some(13));
        let consume = output.clone().expect_output();
        assert_eq!(consume.r#use, 11);
        assert_eq!(consume.def, 13);

        let mapped = output.map(|x| x as u16 + 1);
        let mapped = mapped.expect_output();
        assert_eq!(mapped.r#use, 12);
        assert_eq!(mapped.def, 14);
    }

    #[test]
    fn malloc_source_marks_return_as_owning() {
        run_compiler(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_one() -> *mut i32 {
    malloc(4)
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let alloc_one = find_function(&program, "alloc_one");

                let ret = results
                    .fn_sig(alloc_one)
                    .next()
                    .unwrap()
                    .unwrap()
                    .expect_normal();
                assert_eq!(ret, [Ownership::Owning]);
            },
        );
    }

    #[test]
    fn free_sink_clears_ownership_before_return() {
        run_compiler(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut i32);
}

pub unsafe fn alloc_then_free() -> *mut i32 {
    let p = malloc(4);
    free(p);
    p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let did = find_function(&program, "alloc_then_free");

                // `free` is modeled as a sink, so returning the same pointer should not
                // keep it in an owning state.
                let ret = results.fn_sig(did).next().unwrap().unwrap().expect_normal();
                assert_eq!(ret, [Ownership::Transient]);
            },
        );
    }

    #[test]
    fn ownership_propagates_through_local_function_calls() {
        run_compiler(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc() -> *mut i32 {
    malloc(4)
}

pub unsafe fn wrapper() -> *mut i32 {
    alloc()
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);

                let alloc = find_function(&program, "alloc");
                let wrapper = find_function(&program, "wrapper");

                let alloc_ret = results
                    .fn_sig(alloc)
                    .next()
                    .unwrap()
                    .unwrap()
                    .expect_normal();
                let wrapper_ret = results
                    .fn_sig(wrapper)
                    .next()
                    .unwrap()
                    .unwrap()
                    .expect_normal();

                assert_eq!(alloc_ret, [Ownership::Owning]);
                assert_eq!(wrapper_ret, [Ownership::Owning]);
            },
        );
    }

    #[test]
    fn unknown_foreign_calls_are_treated_conservatively() {
        run_compiler(
            r#"
extern "C" {
    fn mystery(ptr: *mut i32) -> *mut i32;
}

pub unsafe fn passthrough_unknown(p: *mut i32) -> *mut i32 {
    mystery(p)
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let did = find_function(&program, "passthrough_unknown");

                let mut sig = results.fn_sig(did);
                let ret = sig.next().unwrap().unwrap().expect_normal();
                let arg = sig.next().unwrap().unwrap().expect_output();

                // For unknown calls, the analysis borrows the destination and only lends args.
                assert_eq!(ret, [Ownership::Transient]);
                assert_eq!(arg.r#use[0], Ownership::Owning);
                assert_eq!(arg.def[0], Ownership::Owning);
            },
        );
    }

    #[test]
    fn mutable_pointer_to_pointer_argument_becomes_output_param() {
        run_compiler(
            r#"
pub unsafe fn write_out(out: *mut *mut i32, value: *mut i32) {
    *out = value;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let did = find_function(&program, "write_out");

                let mut sig = results.fn_sig(did);
                assert!(sig.next().unwrap().is_none());

                let output_like = sig.next().unwrap().unwrap();
                let passthrough = sig.next().unwrap().unwrap();

                let output_like = output_like.expect_output();
                assert_eq!(output_like.r#use[0], Ownership::Owning);
                assert_eq!(output_like.def[0], Ownership::Owning);
                assert!(matches!(passthrough, Param::Normal(_)));
            },
        );
    }

    #[test]
    fn solidify_marks_return_local_as_owning_for_malloc() {
        run_compiler(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_one() -> *mut i32 {
    malloc(4)
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let solidified = results.solidify(&program);
                let did = find_function(&program, "alloc_one");

                let return_local = Local::from_u32(0);
                let ret_local = solidified.fn_results(&did).local_result(return_local);
                assert_eq!(ret_local, [Ownership::Owning]);
            },
        );
    }

    #[test]
    fn refinement_reaches_high_precision_for_nested_pointer_output() {
        run_compiler(
            r#"
pub unsafe fn write_out(out: *mut *mut i32, value: *mut i32) {
    *out = value;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let did = find_function(&program, "write_out");
                assert!(
                    results.precision(&did) >= 2,
                    "nested pointer flow should keep precision >= 2",
                );

                let solidified = results.solidify(&program);
                let output_param = solidified.fn_results(&did).local_result(Local::from_u32(1));
                assert_eq!(output_param.len(), 2);
                assert_eq!(output_param[0], Ownership::Owning);
            },
        );
    }

    #[test]
    fn refinement_drops_precision_for_conflicting_phi_merge() {
        run_compiler(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn phi_merge(flag: bool, p: *mut i32) -> *mut i32 {
    let mut x: *mut i32 = p;
    if flag {
        x = malloc(4);
    }
    x
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let did = find_function(&program, "phi_merge");
                assert_eq!(
                    results.precision(&did),
                    0,
                    "conflicting phi merge should force conservative precision fallback",
                );

                let solidified = results.solidify(&program);
                let body = tcx.optimized_mir(did);
                let fn_results = solidified.fn_results(&did);

                let ptr_temporaries = body
                    .local_decls
                    .iter_enumerated()
                    .filter(|(local, decl)| {
                        decl.ty.is_raw_ptr() && local.index() > body.arg_count && local.index() != 0
                    })
                    .map(|(local, _)| local)
                    .collect::<Vec<_>>();

                assert!(
                    !ptr_temporaries.is_empty(),
                    "expected at least one pointer temporary around branch merge",
                );

                assert!(ptr_temporaries.iter().all(|&local| {
                    fn_results
                        .local_result(local)
                        .first()
                        .is_none_or(|ownership| !ownership.is_owning())
                }));
            },
        );
    }

    #[test]
    fn solidify_struct_field_results_are_exposed() {
        run_compiler(
            r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn make_holder() -> Holder {
    Holder { p: malloc(4) }
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let solidified = results.solidify(&program);

                let holder = program
                    .structs
                    .iter()
                    .map(|did| did.to_def_id())
                    .find(|&did| tcx.def_path_str(did).rsplit("::").next() == Some("Holder"))
                    .expect("struct `Holder` not found");

                let fields = solidified.struct_results(&holder).collect::<Vec<_>>();
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].len(), 1);
            },
        );
    }
}
