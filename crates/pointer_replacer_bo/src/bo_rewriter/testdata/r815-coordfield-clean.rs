
#![allow(dead_code, unused_mut, unused_unsafe, unused_assignments, unused_variables, non_camel_case_types, non_snake_case)]
pub mod libc {
    pub use core::ffi::c_float;
    pub use core::ffi::c_int;
    pub use core::ffi::c_ulong;
    pub use core::ffi::c_void;
}
pub type uint16_t = u16;
extern "C" {
    fn calloc(n: libc::c_ulong, s: libc::c_ulong) -> *mut libc::c_void;
    fn free(p: *mut libc::c_void);
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct heman_image_s {
    pub width: libc::c_int,
    pub height: libc::c_int,
    pub nbands: libc::c_int,
    pub data: *mut libc::c_float,
}
pub type heman_image = heman_image_s;
unsafe extern "C" fn edt_with_payload(
    mut f: *mut libc::c_float,
    mut d: *mut libc::c_float,
    mut z: *mut libc::c_float,
    mut w: *mut uint16_t,
    mut n: libc::c_int,
    mut payload_in: *mut libc::c_float,
    mut payload_out: *mut libc::c_float,
) {
    let mut i = 0 as libc::c_int;
    while i < n {
        *d.offset(i as isize) = *f.offset(i as isize);
        *z.offset(i as isize) = 0.0f32;
        *w.offset(i as isize) = 0 as uint16_t;
        *payload_out.offset(i as isize) = *payload_in.offset(i as isize);
        i += 1;
    }
}
pub unsafe extern "C" fn entry(mut sdf: *mut heman_image, mut cf: *mut heman_image) {
    transform_to_coordfield(sdf, cf);
}
unsafe extern "C" fn transform_to_coordfield(mut sdf:
        *mut heman_image, mut cf: *mut heman_image) {
    let mut width = (*sdf).width;
    let mut height = (*sdf).height;
    let mut size = width * height;
    let mut ff =
        calloc(size as libc::c_ulong,
                ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as
            *mut libc::c_float;
    let mut dd =
        calloc(size as libc::c_ulong,
                ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as
            *mut libc::c_float;
    let mut zz =
        calloc(((height + 1 as libc::c_int) *
                            (width + 1 as libc::c_int)) as libc::c_ulong,
                ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as
            *mut libc::c_float;
    let mut ww =
        calloc(size as libc::c_ulong,
                ::std::mem::size_of::<uint16_t>() as libc::c_ulong) as
            *mut uint16_t;
    let mut x: libc::c_int = 0;
    x = 0 as libc::c_int;
    while x < width {
        let mut pl1 =
            calloc((height * 2 as libc::c_int) as libc::c_ulong,
                    ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as
                *mut libc::c_float;
        let mut pl2 =
            calloc((height * 2 as libc::c_int) as libc::c_ulong,
                    ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as
                *mut libc::c_float;
        let mut f = ff.offset((height * x) as isize);
        let mut d = dd.offset((height * x) as isize);
        let mut z =
            zz.offset(((height + 1 as libc::c_int) * x) as isize);
        let mut w = ww.offset((height * x) as isize);
        let mut y = 0 as libc::c_int;
        while y < height {
            *f.offset(y as isize) =
                *((*sdf).data).offset(((y * width) as isize) +
                            (x as isize));
            *pl1.offset((y * 2 as libc::c_int) as isize) =
                *((*cf).data).offset(((2 as libc::c_int * (y * width + x))
                                    as isize) + (0 as libc::c_int as isize));
            *pl1.offset((y * 2 as libc::c_int + 1 as libc::c_int) as
                            isize) =
                *((*cf).data).offset(((2 as libc::c_int * (y * width + x))
                                    as isize) + (1 as libc::c_int as isize));
            y += 1;
        }
        edt_with_payload(f, d, z, w, height, pl1, pl2);
        let mut y_0 = 0 as libc::c_int;
        while y_0 < height {
            *((*sdf).data).offset(((y_0 * width) as isize) +
                            (x as isize)) = *d.offset(y_0 as isize);
            *((*cf).data).offset(((2 as libc::c_int * (y_0 * width + x))
                                    as isize) + (0 as libc::c_int as isize)) =
                *pl2.offset((2 as libc::c_int * y_0) as isize);
            *((*cf).data).offset(((2 as libc::c_int * (y_0 * width + x))
                                    as isize) + (1 as libc::c_int as isize)) =
                *pl2.offset((2 as libc::c_int * y_0 + 1 as libc::c_int) as
                            isize);
            y_0 += 1;
        }
        free(pl1 as *mut libc::c_void);
        free(pl2 as *mut libc::c_void);
        x += 1;
    }
    let mut y_1: libc::c_int = 0;
    y_1 = 0 as libc::c_int;
    while y_1 < height {
        let mut pl1_0 =
            calloc((width * 2 as libc::c_int) as libc::c_ulong,
                    ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as
                *mut libc::c_float;
        let mut pl2_0 =
            calloc((width * 2 as libc::c_int) as libc::c_ulong,
                    ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as
                *mut libc::c_float;
        let mut f_0 = ff.offset((width * y_1) as isize);
        let mut d_0 = dd.offset((width * y_1) as isize);
        let mut z_0 =
            zz.offset(((width + 1 as libc::c_int) * y_1) as isize);
        let mut w_0 = ww.offset((width * y_1) as isize);
        let mut x_0 = 0 as libc::c_int;
        while x_0 < width {
            *f_0.offset(x_0 as isize) =
                *((*sdf).data).offset(((y_1 * width) as isize) +
                            (x_0 as isize));
            *pl1_0.offset((x_0 * 2 as libc::c_int) as isize) =
                *((*cf).data).offset(((2 as libc::c_int *
                                            (y_1 * width + x_0)) as isize) +
                            (0 as libc::c_int as isize));
            *pl1_0.offset((x_0 * 2 as libc::c_int + 1 as libc::c_int) as
                            isize) =
                *((*cf).data).offset(((2 as libc::c_int *
                                            (y_1 * width + x_0)) as isize) +
                            (1 as libc::c_int as isize));
            x_0 += 1;
        }
        edt_with_payload(f_0, d_0, z_0, w_0, width, pl1_0, pl2_0);
        let mut x_1 = 0 as libc::c_int;
        while x_1 < width {
            *((*sdf).data).offset(((y_1 * width) as isize) +
                            (x_1 as isize)) = *d_0.offset(x_1 as isize);
            *((*cf).data).offset(((2 as libc::c_int *
                                            (y_1 * width + x_1)) as isize) +
                            (0 as libc::c_int as isize)) =
                *pl2_0.offset((2 as libc::c_int * x_1) as isize);
            *((*cf).data).offset(((2 as libc::c_int *
                                            (y_1 * width + x_1)) as isize) +
                            (1 as libc::c_int as isize)) =
                *pl2_0.offset((2 as libc::c_int * x_1 + 1 as libc::c_int) as
                            isize);
            x_1 += 1;
        }
        free(pl1_0 as *mut libc::c_void);
        free(pl2_0 as *mut libc::c_void);
        y_1 += 1;
    }
    free(ff as *mut libc::c_void);
    free(dd as *mut libc::c_void);
    free(zz as *mut libc::c_void);
    free(ww as *mut libc::c_void);
}
