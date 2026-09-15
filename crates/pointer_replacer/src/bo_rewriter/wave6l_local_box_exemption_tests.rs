//! Wave 6 (R407-12 / R410-8) — the LOCAL-only Box exemption from the owner
//! class's sibling holds: a body-local Box plan that reaches the signature
//! only through receipted bridges changes no signature and no interface
//! class, so the class's `blocked-subject:kind-raw` /
//! `blocked-subject:copy-source-coupled` accounting must not withdraw it.
//! The fixture is ownership-fields' verbatim `heman_ops_percentiles` body
//! (their report 018 claim 8: the 15 heman rows' witness set), copied here
//! so this lane touches none of their files.

use super::{
    RewriteOutcome,
    decision::{Decision, box_facts::BoxShape},
};

fn c_declarations() -> &'static str {
    r#"#![allow(non_camel_case_types)] pub mod libc { pub use core::ffi::c_int; pub use core::ffi::c_ulong; pub use core::ffi::c_float; pub use core::ffi::c_void; } extern "C" { fn malloc(n:libc::c_ulong)->*mut libc::c_void; fn free(p:*mut libc::c_void); }"#
}

fn percentiles_input() -> String {
    format!(
        r#"{}
pub type heman_color = libc::c_uint;
#[repr(C)] #[derive(Copy, Clone)] pub struct heman_image_s {{ pub width: libc::c_int, pub height: libc::c_int, pub nbands: libc::c_int, pub data: *mut libc::c_float }}
pub type heman_image = heman_image_s;
extern "C" {{ fn __assert_fail(a: *const libc::c_char, f: *const libc::c_char, l: libc::c_uint, fun: *const libc::c_char) -> !; }}
unsafe extern "C" fn _match(mut mask: *mut heman_image, mut mask_color: heman_color, mut invert_mask: libc::c_int, mut pixel_index: libc::c_int) -> libc::c_int {{
    let mut mcolor = ((*mask).data).offset((pixel_index * 3 as libc::c_int) as isize);
    ((*mcolor.offset(0 as isize) > 0.5f32) as libc::c_int) ^ invert_mask
}}
{}"#,
        c_declarations().replace("pub mod libc { pub use core::ffi::c_int;", "pub mod libc { pub use core::ffi::c_char; pub use core::ffi::c_uint; pub use core::ffi::c_uchar; pub use core::ffi::c_int;"),
        HEMAN_OPS_PERCENTILES_BODY
    )
}

/// RED (R407-12): both owners decide `Box<[f32]>`; the class
/// `heman_ops_percentiles` is held by its raw parameter siblings (`hmap`,
/// `mask`: `blocked-subject:kind-raw`); the exemption must deliver the two
/// LOCAL owners while the siblings and the signature stay raw.
#[test]
fn w6l_local_only_box_owners_deliver_under_the_sibling_hold() {
    let input = percentiles_input();
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        for name in ["vals", "percentiles"] {
            let (_, decision) = table
                .entries
                .iter()
                .find(|(s, _)| s.param_name.as_deref() == Some(name))
                .unwrap();
            assert!(
                matches!(decision, Decision::Box(plan) if plan.shape == BoxShape::Slice),
                "{name}: {decision:?}"
            );
        }
    })
    .unwrap();
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(&input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        false,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let RewriteOutcome::Emitted {
        source,
        degradations,
        reverted_count,
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    println!("W6L-BOX-EXEMPT-EMITTED\n{source}\nW6L-BOX-EXEMPT-END\n{degradations:?}");
    assert_eq!(reverted_count, 0);
    // The siblings hold: the signature is untouched.
    let compact = source.split_whitespace().collect::<String>();
    assert!(
        compact.contains("fnheman_ops_percentiles(muthmap:*mutheman_image,"),
        "{compact}"
    );
    for sibling in ["heman_ops_percentiles::hmap", "heman_ops_percentiles::mask"] {
        assert!(
            degradations
                .iter()
                .any(|d| d.subject.starts_with(sibling) && d.reason.key() == "kind-raw"),
            "{sibling} stays a typed hold: {degradations:?}"
        );
    }
    // The LOCAL owners deliver.
    for owner in [
        "heman_ops_percentiles::vals#292",
        "heman_ops_percentiles::percentiles#328",
    ] {
        assert!(
            !degradations.iter().any(|d| d.subject == owner),
            "{owner} delivers: {:?}",
            degradations.iter().find(|d| d.subject == owner)
        );
    }
    assert!(
        compact.contains("letmutvals:::std::boxed::Box<[f32]>="),
        "{compact}"
    );
    assert!(
        compact.contains("letmutpercentiles:::std::boxed::Box<[f32]>="),
        "{compact}"
    );
}

const HEMAN_OPS_PERCENTILES_BODY: &str = r#"pub unsafe extern "C" fn heman_ops_percentiles(mut hmap:
        *mut heman_image, mut nsteps: libc::c_int,
    mut mask: *mut heman_image, mut mask_color: heman_color,
    mut invert_mask: libc::c_int, mut offset: libc::c_float)
    -> *mut heman_image {
    if (*hmap).nbands == 1 as libc::c_int
        {} else {
        __assert_fail(b"hmap->nbands == 1\0" as *const u8 as
                *const libc::c_char,
            b"../src/ops.c\0" as *const u8 as *const libc::c_char,
            427 as libc::c_int as libc::c_uint,
            ([b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b'h' as i8,
                            b'e' as i8, b'm' as i8, b'a' as i8, b'n' as i8, b'_' as i8,
                            b'o' as i8, b'p' as i8, b's' as i8, b'_' as i8, b'p' as i8,
                            b'e' as i8, b'r' as i8, b'c' as i8, b'e' as i8, b'n' as i8,
                            b't' as i8, b'i' as i8, b'l' as i8, b'e' as i8, b's' as i8,
                            b'(' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                            b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8, b',' as i8,
                            b' ' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                            b' ' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'c' as i8, b'o' as i8, b'l' as i8,
                            b'o' as i8, b'r' as i8, b',' as i8, b' ' as i8, b'i' as i8,
                            b'n' as i8, b't' as i8, b',' as i8, b' ' as i8, b'f' as i8,
                            b'l' as i8, b'o' as i8, b'a' as i8, b't' as i8, b')' as i8,
                            b'\0' as i8]).as_ptr());
    }
    if mask.is_null() || (*mask).nbands == 3 as libc::c_int
        {} else {
        __assert_fail(b"!mask || mask->nbands == 3\0" as *const u8
                as *const libc::c_char,
            b"../src/ops.c\0" as *const u8 as *const libc::c_char,
            428 as libc::c_int as libc::c_uint,
            ([b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b'h' as i8,
                            b'e' as i8, b'm' as i8, b'a' as i8, b'n' as i8, b'_' as i8,
                            b'o' as i8, b'p' as i8, b's' as i8, b'_' as i8, b'p' as i8,
                            b'e' as i8, b'r' as i8, b'c' as i8, b'e' as i8, b'n' as i8,
                            b't' as i8, b'i' as i8, b'l' as i8, b'e' as i8, b's' as i8,
                            b'(' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                            b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8, b',' as i8,
                            b' ' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                            b' ' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'c' as i8, b'o' as i8, b'l' as i8,
                            b'o' as i8, b'r' as i8, b',' as i8, b' ' as i8, b'i' as i8,
                            b'n' as i8, b't' as i8, b',' as i8, b' ' as i8, b'f' as i8,
                            b'l' as i8, b'o' as i8, b'a' as i8, b't' as i8, b')' as i8,
                            b'\0' as i8]).as_ptr());
    }
    let mut size = (*hmap).height * (*hmap).width;
    let mut src = (*hmap).data;
    let mut minv = 1000 as libc::c_int as libc::c_float;
    let mut maxv = -(1000 as libc::c_int) as libc::c_float;
    let mut npixels = 0 as libc::c_int;
    let mut i = 0 as libc::c_int;
    while i < size {
        if mask.is_null() ||
                _match(mask, mask_color, invert_mask, i) != 0 {
            minv =
                if minv > *src.offset(i as isize) {
                    *src.offset(i as isize)
                } else { minv };
            maxv =
                if maxv > *src.offset(i as isize) {
                    maxv
                } else { *src.offset(i as isize) };
            npixels += 1;
        }
        i += 1;
    }
    let mut vals =
        malloc((::std::mem::size_of::<libc::c_float>() as
                            libc::c_ulong).wrapping_mul(npixels as libc::c_ulong)) as
            *mut libc::c_float;
    npixels = 0 as libc::c_int;
    let mut i_0 = 0 as libc::c_int;
    while i_0 < size {
        if mask.is_null() ||
                _match(mask, mask_color, invert_mask, i_0) != 0 {
            let fresh20 = npixels;
            npixels = npixels + 1;
            *vals.offset(fresh20 as isize) = *src.offset(i_0 as isize);
        }
        i_0 += 1;
    }
    let mut percentiles =
        malloc((::std::mem::size_of::<libc::c_float>() as
                            libc::c_ulong).wrapping_mul(nsteps as libc::c_ulong)) as
            *mut libc::c_float;
    let mut tier = 0 as libc::c_int;
    while tier < nsteps {
        let mut height =
            qselect(vals, npixels, tier * npixels / nsteps);
        *percentiles.offset(tier as isize) = height;
        tier += 1;
    }
    free(vals as *mut libc::c_void);
    let mut i_1 = 0 as libc::c_int;
    while i_1 < size {
        let mut e = *src;
        if mask.is_null() ||
                _match(mask, mask_color, invert_mask, i_1) != 0 {
            let mut tier_0 = nsteps - 1 as libc::c_int;
            while tier_0 >= 0 as libc::c_int {
                if e > *percentiles.offset(tier_0 as isize) {
                    e = *percentiles.offset(tier_0 as isize);
                    break;
                } else { tier_0 -= 1; }
            }
        }
        *src = e + offset;
        let fresh21 = *src;
        src = src.offset(1);
        i_1 += 1;
    }
    free(percentiles as *mut libc::c_void);
    return hmap;
}
unsafe extern "C" fn qselect(mut v: *mut libc::c_float,
    mut len: libc::c_int, mut k: libc::c_int) -> libc::c_float {
    let mut i: libc::c_int = 0;
    let mut st: libc::c_int = 0;
    i = 0 as libc::c_int;
    st = i;
    while i < len - 1 as libc::c_int {
        if !(*v.offset(i as isize) >
                        *v.offset((len - 1 as libc::c_int) as isize)) {
            let mut f = *v.offset(i as isize);
            *v.offset(i as isize) = *v.offset(st as isize);
            *v.offset(st as isize) = f;
            st += 1;
        }
        i += 1;
    }
    let mut __0 = *v.offset((len - 1 as libc::c_int) as isize);
    *v.offset((len - 1 as libc::c_int) as isize) =
        *v.offset(st as isize);
    *v.offset(st as isize) = __0;
    return if k == st {
            *v.offset(st as isize)
        } else if st > k {
            qselect(v, st, k)
        } else { qselect(v.offset(st as isize), len - st, k - st) };
}"#;
