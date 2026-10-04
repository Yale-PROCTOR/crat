// wave-6a relay 145 (R800-4): heman's out-parameter at the frame, its three
// caller shapes. The noise lines are relay 144's fixture
// (w6a-r798-heman-noise.rs); the readers' formals are optional, as the final
// frame decides them (here by a null test, there by the carried nullability);
// `heman_internal_generate_island_noise` and `heman_generate_planet_heightmap`
// are the derived corpus verbatim (rs-crown-derived/heman/lib.rs 6632-6712,
// 6952-7012), `sphere` too (6938-6950); `heman_image_create`, `sin`, `cos`,
// `fabs` are declared.
// From relay 144: `osn_context`,
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
    if ctx.is_null() { return 0.0f64; }
    return *((*ctx).perm).offset(3 as libc::c_int as isize) as libc::c_double + x + y;
}
#[no_mangle]
pub unsafe extern "C" fn open_simplex_noise3(mut ctx: *mut osn_context,
    mut x: libc::c_double, mut y: libc::c_double, mut z: libc::c_double) -> libc::c_double {
    if ctx.is_null() { return 0.0f64; }
    return *((*ctx).permGradIndex3D).offset(3 as libc::c_int as isize) as libc::c_double + x + y + z;
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
#[repr(C)]
#[derive(Copy, Clone)]
pub struct heman_image_s { pub width: libc::c_int, pub height: libc::c_int, pub nbands: libc::c_int, pub data: *mut libc::c_float }
pub type heman_image = heman_image_s;
#[repr(C)]
#[derive(Copy, Clone)]
pub struct kmVec3 { pub x: libc::c_float, pub y: libc::c_float, pub z: libc::c_float }
extern "C" {
    fn heman_image_create(w: libc::c_int, h: libc::c_int, n: libc::c_int) -> *mut heman_image;
    fn sin(_: libc::c_double) -> libc::c_double;
    fn cos(_: libc::c_double) -> libc::c_double;
    fn fabs(_: libc::c_double) -> libc::c_double;
}
#[no_mangle]
pub unsafe extern "C" fn heman_internal_generate_island_noise(mut width:
        libc::c_int, mut height: libc::c_int, mut seed: libc::c_int)
    -> *mut heman_image {
    let mut ctx = 0 as *mut osn_context;
    open_simplex_noise(seed as int64_t, &mut ctx);
    let mut img =
        heman_image_create(width, height, 3 as libc::c_int);
    let mut data = (*img).data;
    let mut invh =
        1.0f32 /
            (if width > height { width } else { height }) as
                libc::c_float;
    let mut invw =
        1.0f32 /
            (if width > height { width } else { height }) as
                libc::c_float;
    let mut freqs: [libc::c_float; 5] =
        [4.0f64 as libc::c_float, 16.0f64 as libc::c_float,
                32.0f64 as libc::c_float, 64.0f64 as libc::c_float,
                128.0f64 as libc::c_float];
    let mut ampls: [libc::c_float; 5] =
        [0.2f64 as libc::c_float, 0.1f64 as libc::c_float,
                0.05f64 as libc::c_float, 0.025f64 as libc::c_float,
                0.0125f64 as libc::c_float];
    let mut y: libc::c_int = 0;
    y = 0 as libc::c_int;
    while y < height {
        let mut v = y as libc::c_float * invh;
        let mut dst =
            data.offset((y * width * 3 as libc::c_int) as isize);
        let mut x = 0 as libc::c_int;
        while x < width {
            let mut u = x as libc::c_float * invw;
            *dst =
                (ampls[0 as libc::c_int as usize] as libc::c_double *
                                    open_simplex_noise2(ctx,
                                        (u * freqs[0 as libc::c_int as usize]) as libc::c_double,
                                        (v * freqs[0 as libc::c_int as usize]) as libc::c_double) +
                                ampls[1 as libc::c_int as usize] as libc::c_double *
                                    open_simplex_noise2(ctx,
                                        (u * freqs[1 as libc::c_int as usize]) as libc::c_double,
                                        (v * freqs[1 as libc::c_int as usize]) as libc::c_double) +
                            ampls[2 as libc::c_int as usize] as libc::c_double *
                                open_simplex_noise2(ctx,
                                    (u * freqs[2 as libc::c_int as usize]) as libc::c_double,
                                    (v * freqs[2 as libc::c_int as usize]) as libc::c_double))
                    as libc::c_float;
            let fresh0 = *dst;
            dst = dst.offset(1);
            *dst =
                (ampls[3 as libc::c_int as usize] as libc::c_double *
                                open_simplex_noise2(ctx,
                                    (u * freqs[3 as libc::c_int as usize]) as libc::c_double,
                                    (v * freqs[3 as libc::c_int as usize]) as libc::c_double) +
                            ampls[4 as libc::c_int as usize] as libc::c_double *
                                open_simplex_noise2(ctx,
                                    (u * freqs[4 as libc::c_int as usize]) as libc::c_double,
                                    (v * freqs[4 as libc::c_int as usize]) as libc::c_double))
                    as libc::c_float;
            let fresh1 = *dst;
            dst = dst.offset(1);
            u = (u as libc::c_double + 0.5f64) as libc::c_float;
            *dst =
                (ampls[3 as libc::c_int as usize] as libc::c_double *
                                open_simplex_noise2(ctx,
                                    (u * freqs[3 as libc::c_int as usize]) as libc::c_double,
                                    (v * freqs[3 as libc::c_int as usize]) as libc::c_double) +
                            ampls[4 as libc::c_int as usize] as libc::c_double *
                                open_simplex_noise2(ctx,
                                    (u * freqs[4 as libc::c_int as usize]) as libc::c_double,
                                    (v * freqs[4 as libc::c_int as usize]) as libc::c_double))
                    as libc::c_float;
            let fresh2 = *dst;
            dst = dst.offset(1);
            x += 1;
        }
        y += 1;
    }
    open_simplex_noise_free(ctx);
    return img;
}
unsafe extern "C" fn sphere(mut u: libc::c_float,
    mut v: libc::c_float, mut r: libc::c_float,
    mut dst: *mut kmVec3) {
    (*dst).x =
        (r as libc::c_double * sin(v as libc::c_double) *
                    cos(u as libc::c_double)) as libc::c_float;
    (*dst).y =
        (r as libc::c_double * cos(v as libc::c_double)) as
            libc::c_float;
    (*dst).z =
        (r as libc::c_double * -sin(v as libc::c_double) *
                    sin(u as libc::c_double)) as libc::c_float;
}
#[no_mangle]
pub unsafe extern "C" fn heman_generate_planet_heightmap(mut width:
        libc::c_int, mut height: libc::c_int, mut seed: libc::c_int)
    -> *mut heman_image {
    let mut ctx = 0 as *mut osn_context;
    open_simplex_noise(seed as int64_t, &mut ctx);
    let mut result =
        heman_image_create(width, height, 1 as libc::c_int);
    let mut scalex =
        (2.0f32 as libc::c_double * 3.1415926535f64 /
                    width as libc::c_double) as libc::c_float;
    let mut scaley =
        (3.1415926535f64 / height as libc::c_double) as
            libc::c_float;
    let mut invh = 1.0f32 / height as libc::c_float;
    let mut y: libc::c_int = 0;
    y = 0 as libc::c_int;
    while y < height {
        let mut dst = ((*result).data).offset((y * width) as isize);
        let mut p = kmVec3 { x: 0., y: 0., z: 0. };
        let mut v = y as libc::c_float * invh;
        let mut s = 0.95f64 as libc::c_float;
        let mut antarctic_influence =
            (if (10 as libc::c_int as libc::c_float * (v - s) / s) as
                                libc::c_double > -0.5f64 {
                        (10 as libc::c_int as libc::c_float * (v - s) / s) as
                            libc::c_double
                    } else { -0.5f64 }) as libc::c_float;
        v = fabs(v as libc::c_double - 0.5f64) as libc::c_float;
        v =
            (1.5f64 * (0.5f64 - v as libc::c_double)) as libc::c_float;
        let mut equatorial_influence = v * v;
        v = y as libc::c_float * scaley;
        let mut x = 0 as libc::c_int;
        while x < width {
            let mut u = x as libc::c_float * scalex;
            let mut freq = 1 as libc::c_int as libc::c_float;
            let mut amp = 1 as libc::c_int as libc::c_float;
            let mut h = antarctic_influence + equatorial_influence;
            let mut oct = 0 as libc::c_int;
            while oct < 6 as libc::c_int {
                sphere(u, v, freq, &mut p);
                h =
                    (h as libc::c_double +
                                amp as libc::c_double *
                                    open_simplex_noise3(ctx, p.x as libc::c_double,
                                        p.y as libc::c_double, p.z as libc::c_double)) as
                        libc::c_float;
                amp = (amp as libc::c_double * 0.5f64) as libc::c_float;
                freq *= 2 as libc::c_int as libc::c_float;
                oct += 1;
            }
            *dst = h;
            let fresh10 = *dst;
            dst = dst.offset(1);
            x += 1;
        }
        y += 1;
    }
    open_simplex_noise_free(ctx);
    return result;
}
