//! tulipindicators, reduced: the flexible-tail `ti_buffer` (`double vals[1]`
//! struct hack), its allocating callee `ti_buffer_new`, its freeing callee
//! `ti_buffer_free`, one indicator (`ti_cci`'s buffer loop) and the smoke
//! test's `test_buffer`. Types spelled as the derived corpus spells them.

pub(super) const TULIP_BUFFER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(_: std::os::raw::c_ulong) -> *mut std::os::raw::c_void;
    fn free(_: *mut std::os::raw::c_void);
    fn fabs(_: std::os::raw::c_double) -> std::os::raw::c_double;
}
#[repr(C)]
pub struct ti_buffer {
    pub size: std::os::raw::c_int,
    pub pushes: std::os::raw::c_int,
    pub index: std::os::raw::c_int,
    pub sum: std::os::raw::c_double,
    pub vals: [std::os::raw::c_double; 1],
}
#[automatically_derived]
impl ::core::marker::Copy for ti_buffer { }
#[automatically_derived]
impl ::core::clone::Clone for ti_buffer {
    #[inline]
    fn clone(&self) -> ti_buffer { *self }
}
#[no_mangle]
pub unsafe extern "C" fn ti_buffer_new(mut size: std::os::raw::c_int) -> *mut ti_buffer {
    let s: std::os::raw::c_int = ::std::mem::size_of::<ti_buffer>() as std::os::raw::c_ulong as std::os::raw::c_int
        + (size - 1 as std::os::raw::c_int) * ::std::mem::size_of::<std::os::raw::c_double>() as std::os::raw::c_ulong as std::os::raw::c_int;
    let mut ret: *mut ti_buffer = malloc(s as std::os::raw::c_uint as std::os::raw::c_ulong) as *mut ti_buffer;
    (*ret).size = size;
    (*ret).pushes = 0 as std::os::raw::c_int;
    (*ret).index = 0 as std::os::raw::c_int;
    (*ret).sum = 0 as std::os::raw::c_int as std::os::raw::c_double;
    return ret;
}
#[no_mangle]
pub unsafe extern "C" fn ti_buffer_free(mut buffer: *mut ti_buffer) {
    free(buffer as *mut std::os::raw::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn ti_cci(mut size: std::os::raw::c_int, mut inputs: *const *const std::os::raw::c_double, mut period: std::os::raw::c_int, mut outputs: *const *mut std::os::raw::c_double) -> std::os::raw::c_int {
    let high: *const std::os::raw::c_double = *inputs.offset(0 as std::os::raw::c_int as isize);
    let low: *const std::os::raw::c_double = *inputs.offset(1 as std::os::raw::c_int as isize);
    let close: *const std::os::raw::c_double = *inputs.offset(2 as std::os::raw::c_int as isize);
    let scale: std::os::raw::c_double = 1.0f64 / period as std::os::raw::c_double;
    if period < 1 as std::os::raw::c_int {
        return 1 as std::os::raw::c_int;
    }
    let mut output: *mut std::os::raw::c_double = *outputs.offset(0 as std::os::raw::c_int as isize);
    let mut sum: *mut ti_buffer = ti_buffer_new(period);
    let mut i: std::os::raw::c_int = 0;
    let mut j: std::os::raw::c_int = 0;
    i = 0 as std::os::raw::c_int;
    while i < size {
        let today: std::os::raw::c_double = (*high.offset(i as isize) + *low.offset(i as isize) + *close.offset(i as isize)) * (1.0f64 / 3.0f64);
        if (*sum).pushes >= (*sum).size {
            (*sum).sum -= *(*sum).vals.as_mut_ptr().offset((*sum).index as isize)
        }
        (*sum).sum += today;
        *(*sum).vals.as_mut_ptr().offset((*sum).index as isize) = today;
        (*sum).pushes += 1 as std::os::raw::c_int;
        (*sum).index = (*sum).index + 1 as std::os::raw::c_int;
        if (*sum).index >= (*sum).size {
            (*sum).index = 0 as std::os::raw::c_int
        }
        let avg: std::os::raw::c_double = (*sum).sum * scale;
        if i >= period * 2 as std::os::raw::c_int - 2 as std::os::raw::c_int {
            let mut acc: std::os::raw::c_double = 0 as std::os::raw::c_int as std::os::raw::c_double;
            j = 0 as std::os::raw::c_int;
            while j < period {
                acc += fabs(avg - *(*sum).vals.as_mut_ptr().offset(j as isize));
                j += 1
            }
            let mut cci: std::os::raw::c_double = acc * scale;
            cci *= 0.015f64;
            cci = (today - avg) / cci;
            let fresh0 = output;
            output = output.offset(1);
            *fresh0 = cci
        }
        i += 1
    }
    ti_buffer_free(sum);
    return 0 as std::os::raw::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn test_buffer() -> std::os::raw::c_int {
    let mut fails: std::os::raw::c_int = 0;
    let mut b: *mut ti_buffer = ti_buffer_new(3 as std::os::raw::c_int);
    if (*b).pushes >= (*b).size {
        (*b).sum -= *(*b).vals.as_mut_ptr().offset((*b).index as isize)
    }
    (*b).sum += 5.0f64;
    *(*b).vals.as_mut_ptr().offset((*b).index as isize) = 5.0f64;
    (*b).pushes += 1 as std::os::raw::c_int;
    (*b).index = (*b).index + 1 as std::os::raw::c_int;
    if (*b).index >= (*b).size { (*b).index = 0 as std::os::raw::c_int }
    if fabs((*b).sum - 5.0f64) > 0.001f64 {
        fails += 1;
    }
    if fabs(*(*b).vals.as_mut_ptr().offset((((*b).index + (*b).size - 1 as std::os::raw::c_int + -(1 as std::os::raw::c_int)) % (*b).size) as isize) - 5.0f64) > 0.001f64 {
        fails += 1;
    }
    ti_buffer_free(b);
    return fails;
}
"#;

/// The shared header of every tulip fixture: the struct, its c2rust-spelled
/// `Copy` / `Clone` impls, `ti_buffer_new`, `ti_buffer_free`.
pub(super) const TULIP_HEADER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(_: std::os::raw::c_ulong) -> *mut std::os::raw::c_void;
    fn free(_: *mut std::os::raw::c_void);
    fn fabs(_: std::os::raw::c_double) -> std::os::raw::c_double;
}
#[repr(C)]
pub struct ti_buffer {
    pub size: std::os::raw::c_int,
    pub pushes: std::os::raw::c_int,
    pub index: std::os::raw::c_int,
    pub sum: std::os::raw::c_double,
    pub vals: [std::os::raw::c_double; 1],
}
#[automatically_derived]
impl ::core::marker::Copy for ti_buffer { }
#[automatically_derived]
impl ::core::clone::Clone for ti_buffer {
    #[inline]
    fn clone(&self) -> ti_buffer { *self }
}
#[no_mangle]
pub unsafe extern "C" fn ti_buffer_new(mut size: std::os::raw::c_int) -> *mut ti_buffer {
    let s: std::os::raw::c_int = ::std::mem::size_of::<ti_buffer>() as std::os::raw::c_ulong as std::os::raw::c_int
        + (size - 1 as std::os::raw::c_int) * ::std::mem::size_of::<std::os::raw::c_double>() as std::os::raw::c_ulong as std::os::raw::c_int;
    let mut ret: *mut ti_buffer = malloc(s as std::os::raw::c_uint as std::os::raw::c_ulong) as *mut ti_buffer;
    (*ret).size = size;
    (*ret).pushes = 0 as std::os::raw::c_int;
    (*ret).index = 0 as std::os::raw::c_int;
    (*ret).sum = 0 as std::os::raw::c_int as std::os::raw::c_double;
    return ret;
}
#[no_mangle]
pub unsafe extern "C" fn ti_buffer_free(mut buffer: *mut ti_buffer) {
    free(buffer as *mut std::os::raw::c_void);
}
"#;

/// tulip `ti_stoch`, reduced: TWO buffers in one owner (`k_sum`, `d_sum`),
/// the second fed from the first's running mean, both freed at the end.
pub(super) const TULIP_STOCH_BODY: &str = r#"
#[no_mangle]
pub unsafe extern "C" fn ti_stoch(mut size: std::os::raw::c_int, mut high: *const std::os::raw::c_double, mut kslow: std::os::raw::c_int, mut dperiod: std::os::raw::c_int, mut output: *mut std::os::raw::c_double) -> std::os::raw::c_int {
    let kper: std::os::raw::c_double = 1.0f64 / kslow as std::os::raw::c_double;
    let dper: std::os::raw::c_double = 1.0f64 / dperiod as std::os::raw::c_double;
    let mut k_sum: *mut ti_buffer = ti_buffer_new(kslow);
    let mut d_sum: *mut ti_buffer = ti_buffer_new(dperiod);
    let mut i: std::os::raw::c_int = 0;
    i = 0 as std::os::raw::c_int;
    while i < size {
        let kfast: std::os::raw::c_double = *high.offset(i as isize);
        if (*k_sum).pushes >= (*k_sum).size {
            (*k_sum).sum -= *(*k_sum).vals.as_mut_ptr().offset((*k_sum).index as isize)
        }
        (*k_sum).sum += kfast;
        *(*k_sum).vals.as_mut_ptr().offset((*k_sum).index as isize) = kfast;
        (*k_sum).pushes += 1 as std::os::raw::c_int;
        (*k_sum).index = (*k_sum).index + 1 as std::os::raw::c_int;
        if (*k_sum).index >= (*k_sum).size {
            (*k_sum).index = 0 as std::os::raw::c_int
        }
        if i >= kslow - 1 as std::os::raw::c_int {
            let k: std::os::raw::c_double = (*k_sum).sum * kper;
            if (*d_sum).pushes >= (*d_sum).size {
                (*d_sum).sum -= *(*d_sum).vals.as_mut_ptr().offset((*d_sum).index as isize)
            }
            (*d_sum).sum += k;
            *(*d_sum).vals.as_mut_ptr().offset((*d_sum).index as isize) = k;
            (*d_sum).pushes += 1 as std::os::raw::c_int;
            (*d_sum).index = (*d_sum).index + 1 as std::os::raw::c_int;
            if (*d_sum).index >= (*d_sum).size {
                (*d_sum).index = 0 as std::os::raw::c_int
            }
            if i >= kslow + dperiod - 2 as std::os::raw::c_int {
                let fresh1 = output;
                output = output.offset(1);
                *fresh1 = (*d_sum).sum * dper
            }
        }
        i += 1
    }
    ti_buffer_free(k_sum);
    ti_buffer_free(d_sum);
    return 0 as std::os::raw::c_int;
}
"#;

/// Control: the struct crosses a foreign boundary (an extern consumer takes it
/// by pointer), so the layout may not change — every row stays held.
pub(super) const TULIP_CROSSING_BODY: &str = r#"
extern "C" {
    fn ti_buffer_dump(buffer: *mut ti_buffer);
}
#[no_mangle]
pub unsafe extern "C" fn crossing() -> std::os::raw::c_int {
    let mut b: *mut ti_buffer = ti_buffer_new(3 as std::os::raw::c_int);
    *(*b).vals.as_mut_ptr().offset((*b).index as isize) = 5.0f64;
    ti_buffer_dump(b);
    ti_buffer_free(b);
    return 0 as std::os::raw::c_int;
}
"#;

/// Control: a caller keeps using the buffer after handing it to the freeing
/// callee (a use after free in the input — not a UB-free input, so nothing is
/// owed there — but the transaction must not claim an owning transfer).
pub(super) const TULIP_RETAINED_BODY: &str = r#"
#[no_mangle]
pub unsafe extern "C" fn retained() -> std::os::raw::c_int {
    let mut b: *mut ti_buffer = ti_buffer_new(3 as std::os::raw::c_int);
    *(*b).vals.as_mut_ptr().offset((*b).index as isize) = 5.0f64;
    ti_buffer_free(b);
    return (*b).pushes;
}
"#;
