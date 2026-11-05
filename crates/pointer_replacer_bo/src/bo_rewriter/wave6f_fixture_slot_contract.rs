#![feature(derive_clone_copy)]
// w6f-slot-contract-frame
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut ::std::ffi::c_void;
    fn free(ptr: *mut ::std::ffi::c_void);
}
pub struct Mem {
    pub opaque: *mut ::std::ffi::c_void,
    pub free_func: Option<unsafe extern "C" fn(*mut ::std::ffi::c_void, *mut ::std::ffi::c_void)>,
}
pub struct Holder {
    pub count: i32,
    pub slot_: *mut i32,
}
unsafe extern "C" fn CustomFree(mut m: *mut Mem, mut p: *mut ::std::ffi::c_void) {
    if !p.is_null() {
        ((*m).free_func).expect("non-null function pointer")((*m).opaque, p);
    }
}
unsafe extern "C" fn HolderFree(mut m: *mut Mem, mut h: *mut Holder) {
    CustomFree(m, (*h).slot_ as *mut ::std::ffi::c_void);
    let ref mut fresh1 = (*h).slot_;
    *fresh1 = 0 as *mut i32;
}
unsafe extern "C" fn HolderFill(mut m: *mut Mem, mut h: *mut Holder, mut value: i32) {
    let mut fresh = malloc(::std::mem::size_of::<i32>()) as *mut i32;
    *fresh = value;
    if !((*h).slot_).is_null() {
        (*h).count = *(*h).slot_;
        HolderFree(m, h);
    }
    let ref mut fresh2 = (*h).slot_;
    *fresh2 = fresh;
}
unsafe extern "C" fn HolderNew() -> *mut Holder {
    let mut h = malloc(::std::mem::size_of::<Holder>()) as *mut Holder;
    (*h).count = 0 as i32;
    let ref mut fresh3 = (*h).slot_;
    *fresh3 = 0 as *mut i32;
    return h;
}
#[no_mangle]
pub unsafe extern "C" fn drive(mut m: *mut Mem, mut value: i32) -> i32 {
    let mut h = HolderNew();
    HolderFill(m, h, value);
    HolderFill(m, h, value + 1);
    let mut v = *(*h).slot_ + (*h).count;
    HolderFree(m, h);
    free(h as *mut ::std::ffi::c_void);
    return v;
}
