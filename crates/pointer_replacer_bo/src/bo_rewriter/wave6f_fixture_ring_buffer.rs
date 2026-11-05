#![feature(derive_clone_copy)]
// w6f-ring-buffer-frame
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut ::std::ffi::c_void;
    fn free(ptr: *mut ::std::ffi::c_void);
    fn memcpy(_: *mut ::std::ffi::c_void, _: *const ::std::ffi::c_void, _: usize) -> *mut ::std::ffi::c_void;
}
pub struct RingBuffer {
    pub cur_size_: u32,
    pub data_: *mut u8,
    pub buffer_: *mut u8,
}
unsafe extern "C" fn RingBufferFree(mut rb: *mut RingBuffer) {
    free((*rb).data_ as *mut ::std::ffi::c_void);
    (*rb).data_ = 0 as *mut u8;
}
unsafe extern "C" fn RingBufferInitBuffer(buflen: u32, mut rb: *mut RingBuffer) {
    let mut new_data = malloc((2 as u32).wrapping_add(buflen) as usize) as *mut u8;
    if !((*rb).data_).is_null() {
        memcpy(new_data as *mut ::std::ffi::c_void, (*rb).data_ as *const ::std::ffi::c_void, (2 as u32).wrapping_add((*rb).cur_size_) as usize);
        free((*rb).data_ as *mut ::std::ffi::c_void);
        (*rb).data_ = 0 as *mut u8;
    }
    (*rb).data_ = new_data;
    (*rb).cur_size_ = buflen;
    (*rb).buffer_ = ((*rb).data_).offset(2 as isize);
    *((*rb).buffer_).offset(-(1 as isize)) = 0 as u8;
}
unsafe extern "C" fn RingBufferPeek(mut rb: *mut RingBuffer, mut i: u32) -> u8 {
    return *((*rb).data_).offset(i as isize);
}
#[no_mangle]
pub unsafe extern "C" fn drive(buflen: u32) -> u8 {
    let mut rb = RingBuffer { cur_size_: 0, data_: 0 as *mut u8, buffer_: 0 as *mut u8 };
    RingBufferInitBuffer(buflen, &mut rb);
    RingBufferInitBuffer(buflen, &mut rb);
    let mut v = RingBufferPeek(&mut rb, 1 as u32);
    RingBufferFree(&mut rb);
    return v;
}
