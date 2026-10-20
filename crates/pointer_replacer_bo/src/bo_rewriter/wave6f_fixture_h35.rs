#![feature(derive_clone_copy)]
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types, non_snake_case)]
pub type size_t = u64;
pub struct BrotliEncoderParams {
    pub quality: i32,
    pub lgwin: i32,
}
pub struct H35 {
    pub fresh: i32,
    pub params: *const BrotliEncoderParams,
}
unsafe extern "C" fn HashMemAllocInBytesH35(
    mut params: *const BrotliEncoderParams,
    mut one_shot: i32,
    mut input_size: size_t,
) -> size_t {
    return ((*params).lgwin as size_t).wrapping_add(input_size);
}
unsafe extern "C" fn InitializeH35(mut self_0: *mut H35, mut params: *const BrotliEncoderParams) {
    (*self_0).fresh = 1 as i32;
    let ref mut fresh15 = (*self_0).params;
    *fresh15 = params;
}
unsafe extern "C" fn PrepareH35(mut self_0: *mut H35, mut one_shot: i32, mut input_size: size_t) -> size_t {
    return HashMemAllocInBytesH35((*self_0).params, one_shot, input_size);
}
#[no_mangle]
pub unsafe extern "C" fn HasherSetupH35(mut h: *mut H35, mut params: *const BrotliEncoderParams, mut input_size: size_t) -> size_t {
    InitializeH35(h, params);
    return PrepareH35(h, 0 as i32, input_size);
}
