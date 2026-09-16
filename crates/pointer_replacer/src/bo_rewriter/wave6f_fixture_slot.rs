#![feature(derive_clone_copy)]
// w6f-slot-frame
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut ::std::ffi::c_void;
    fn free(ptr: *mut ::std::ffi::c_void);
    fn memcpy(_: *mut ::std::ffi::c_void, _: *const ::std::ffi::c_void, _: usize) -> *mut ::std::ffi::c_void;
}
pub struct Holder {
    pub count: i32,
    pub slot_: *mut i32,
}
unsafe extern "C" fn HolderFree(mut h: *mut Holder) {
    free((*h).slot_ as *mut ::std::ffi::c_void);
    let ref mut fresh1 = (*h).slot_;
    *fresh1 = 0 as *mut i32;
}
unsafe extern "C" fn HolderFill(mut h: *mut Holder, mut value: i32) {
    let mut fresh = malloc(::std::mem::size_of::<i32>()) as *mut i32;
    *fresh = value;
    if !((*h).slot_).is_null() {
        let mut copy: i32 = 0;
        memcpy(&mut copy as *mut i32 as *mut ::std::ffi::c_void, (*h).slot_ as *const ::std::ffi::c_void, ::std::mem::size_of::<i32>());
        (*h).count = copy;
        HolderFree(h);
    }
    let ref mut fresh2 = (*h).slot_;
    *fresh2 = fresh;
}
unsafe extern "C" fn HolderPeek(mut h: *mut Holder) -> i32 {
    return *(*h).slot_;
}
#[no_mangle]
pub unsafe extern "C" fn drive(mut value: i32) -> i32 {
    let mut h = Holder { count: 0, slot_: 0 as *mut i32 };
    HolderFill(&mut h, value);
    HolderFill(&mut h, value + 1);
    let mut v = HolderPeek(&mut h) + h.count;
    HolderFree(&mut h);
    return v;
}
