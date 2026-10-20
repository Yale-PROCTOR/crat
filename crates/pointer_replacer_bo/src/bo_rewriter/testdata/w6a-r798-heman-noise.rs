// wave-6a relay 144 (R798-3): heman's out-parameter allocator. `osn_context`,
// `allocate_perm`, `open_simplex_noise` and `open_simplex_noise_free` are the
// derived corpus lines verbatim (rs-crown-derived/heman/lib.rs 8164-8167,
// 8584-8608, 8636-8695, 8697-8709); the reader is reduced (the corpus
// `open_simplex_noise2` reads `(*ctx).perm` through 130 lines of gradients) and
// the caller is `heman_generate_simplex_fbm`'s ctx lines.
#![allow(dead_code, unused_mut, unused_unsafe, unused_assignments, unused_variables, non_camel_case_types, non_snake_case)]
pub mod libc {
    pub use core::ffi::c_double;
    pub use core::ffi::c_float;
    pub use core::ffi::c_int;
    pub use core::ffi::c_long;
    pub use core::ffi::c_longlong;
    pub use core::ffi::c_schar;
    pub use core::ffi::c_short;
    pub use core::ffi::c_ulong;
    pub use core::ffi::c_void;
}
pub type int16_t = i16;
pub type int64_t = i64;
extern "C" {
    fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
    fn free(_: *mut libc::c_void);
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct osn_context {
    pub perm: *mut int16_t,
    pub permGradIndex3D: *mut int16_t,
}
unsafe extern "C" fn allocate_perm(mut ctx: *mut osn_context,
    mut nperm: libc::c_int, mut ngrad: libc::c_int)
    -> libc::c_int {
    if !((*ctx).perm).is_null() {
        free((*ctx).perm as *mut libc::c_void);
    }
    if !((*ctx).permGradIndex3D).is_null() {
        free((*ctx).permGradIndex3D as *mut libc::c_void);
    }
    (*ctx).perm =
        malloc((::std::mem::size_of::<int16_t>() as
                            libc::c_ulong).wrapping_mul(nperm as libc::c_ulong)) as
            *mut int16_t;
    if ((*ctx).perm).is_null() { return -(12 as libc::c_int); }
    (*ctx).permGradIndex3D =
        malloc((::std::mem::size_of::<int16_t>() as
                            libc::c_ulong).wrapping_mul(ngrad as libc::c_ulong)) as
            *mut int16_t;
    if ((*ctx).permGradIndex3D).is_null() {
        free((*ctx).perm as *mut libc::c_void);
        return -(12 as libc::c_int);
    }
    return 0 as libc::c_int;
}
#[no_mangle]
#[no_mangle]
pub unsafe extern "C" fn open_simplex_noise(mut seed: int64_t,
    mut ctx: *mut *mut osn_context) -> libc::c_int {
    let mut rc: libc::c_int = 0;
    let mut source: [int16_t; 256] = [0; 256];
    let mut i: libc::c_int = 0;
    let mut perm = 0 as *mut int16_t;
    let mut permGradIndex3D = 0 as *mut int16_t;
    *ctx =
        malloc(::std::mem::size_of::<osn_context>() as
                    libc::c_ulong) as *mut osn_context;
    if (*ctx).is_null() { return -(12 as libc::c_int); }
    (**ctx).perm = 0 as *mut int16_t;
    (**ctx).permGradIndex3D = 0 as *mut int16_t;
    rc =
        allocate_perm(*ctx, 256 as libc::c_int, 256 as libc::c_int);
    if rc != 0 { free(*ctx as *mut libc::c_void); return rc; }
    perm = (**ctx).perm;
    permGradIndex3D = (**ctx).permGradIndex3D;
    i = 0 as libc::c_int;
    while i < 256 as libc::c_int {
        source[i as usize] = i as int16_t;
        i += 1;
    }
    seed =
        (seed as libc::c_longlong *
                        6364136223846793005 as libc::c_longlong +
                    1442695040888963407 as libc::c_longlong) as int64_t;
    seed =
        (seed as libc::c_longlong *
                        6364136223846793005 as libc::c_longlong +
                    1442695040888963407 as libc::c_longlong) as int64_t;
    seed =
        (seed as libc::c_longlong *
                        6364136223846793005 as libc::c_longlong +
                    1442695040888963407 as libc::c_longlong) as int64_t;
    i = 255 as libc::c_int;
    while i >= 0 as libc::c_int {
        seed =
            (seed as libc::c_longlong *
                            6364136223846793005 as libc::c_longlong +
                        1442695040888963407 as libc::c_longlong) as int64_t;
        let mut r =
            ((seed + 31 as libc::c_int as libc::c_long) %
                        (i + 1 as libc::c_int) as libc::c_long) as libc::c_int;
        if r < 0 as libc::c_int { r += i + 1 as libc::c_int; }
        *perm.offset(i as isize) = source[r as usize];
        *permGradIndex3D.offset(i as isize) =
            (*perm.offset(i as isize) as
                                libc::c_ulong).wrapping_rem((::std::mem::size_of::<[libc::c_schar; 72]>()
                                        as
                                        libc::c_ulong).wrapping_div(::std::mem::size_of::<libc::c_schar>()
                                    as
                                    libc::c_ulong).wrapping_div(3 as libc::c_int as
                                libc::c_ulong)).wrapping_mul(3 as libc::c_int as
                        libc::c_ulong) as libc::c_short;
        source[r as usize] = source[i as usize];
        i -= 1;
    }
    return 0 as libc::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn open_simplex_noise_free(mut ctx:
        *mut osn_context) {
    if ctx.is_null() { return; }
    if !((*ctx).perm).is_null() {
        free((*ctx).perm as *mut libc::c_void);
        (*ctx).perm = 0 as *mut int16_t;
    }
    if !((*ctx).permGradIndex3D).is_null() {
        free((*ctx).permGradIndex3D as *mut libc::c_void);
        (*ctx).permGradIndex3D = 0 as *mut int16_t;
    }
    free(ctx as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn open_simplex_noise2(mut ctx: *mut osn_context,
    mut x: libc::c_double, mut y: libc::c_double) -> libc::c_double {
    return *((*ctx).perm).offset(3 as libc::c_int as isize) as libc::c_double + x + y;
}
#[no_mangle]
pub unsafe extern "C" fn heman_generate_simplex_fbm(mut width: libc::c_int,
    mut seed: libc::c_int) -> libc::c_double {
    let mut ctx = 0 as *mut osn_context;
    open_simplex_noise(seed as int64_t, &mut ctx);
    let mut acc = 0.0f64;
    let mut x = 0 as libc::c_int;
    while x < width {
        acc += open_simplex_noise2(ctx, x as libc::c_double, 0.5f64);
        x += 1;
    }
    open_simplex_noise_free(ctx);
    return acc;
}
