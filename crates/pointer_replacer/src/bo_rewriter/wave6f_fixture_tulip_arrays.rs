// w6f-tulip-arrays-frame
// tulipindicators' array locals as the derived substrate spells them
// (`benchmarks/rs-crown-derived/tulipindicators/c2rust-lib.rs`): the census's
// eleven `array-local-incomplete:initializer` rows are element LISTS, not the
// repeat form — `fuzzer::stress`'s null lists, `example1::main_0`'s value
// list. The whole array is then handed to a callee as `inputs.as_ptr()`.
#![allow(
    dead_code,
    unused_mut,
    unused_unsafe,
    unused_assignments,
    unused_variables,
    non_camel_case_types,
    non_snake_case
)]
pub unsafe extern "C" fn ti_sma(
    mut size: i32,
    mut inputs: *const *const f64,
    mut options: *const f64,
) -> i32 {
    let mut in_0 = *inputs.offset(0 as isize);
    return (*in_0 > *options) as i32;
}
pub unsafe extern "C" fn stress(mut data_in: *const f64, mut data_out: *mut f64) -> i32 {
    let mut inputs: [*const f64; 4] = [
        0 as *const f64,
        0 as *const f64,
        0 as *const f64,
        0 as *const f64,
    ];
    let mut options: [f64; 1] = [0.];
    inputs[0 as usize] = data_in;
    inputs[1 as usize] = data_in;
    let mut probe = inputs[2 as usize];
    return ti_sma(1 as i32, inputs.as_ptr(), options.as_ptr());
}
pub unsafe extern "C" fn empty_0(mut data_in: *const f64) -> i32 {
    let mut none_at_all: [*const f64; 0] = [];
    return none_at_all.as_ptr().is_null() as i32;
}
pub unsafe extern "C" fn main_0(mut data_in: *const f64, mut data_out: *mut f64) -> i32 {
    let mut all_inputs: [*const f64; 1] = [data_in];
    let mut options: [f64; 1] = [0.];
    return ti_sma(1 as i32, all_inputs.as_ptr(), options.as_ptr());
}

// tulip's OTHER value lists: the elements are buffers (a local array's
// `as_ptr`, a C string literal), whose readers index past the first element.
pub unsafe extern "C" fn buffers(mut size: i32) -> i32 {
    let mut scratch: [f64; 4] = [0.; 4];
    let mut inputs: [*const f64; 1] = [scratch.as_ptr()];
    return ti_sma(size, inputs.as_ptr(), scratch.as_ptr());
}
